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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toConfigOptions(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1;
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
v___x_157_ = l_instMonadEIO___redArg();
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
v___x_333_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_345_; lean_object* v_env_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v___x_347_ = lean_st_ref_get(v___y_341_);
v___x_348_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_340_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_toCold_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_371_; 
v_toCold_349_ = lean_ctor_get(v___y_342_, 0);
v_a_350_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_371_ == 0)
{
v___x_352_ = v___x_348_;
v_isShared_353_ = v_isSharedCheck_371_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_348_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_371_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_lctx_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_369_; 
v_lctx_354_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_347_, 1);
lean_dec(v_unused_370_);
v___x_356_ = v___x_347_;
v_isShared_357_ = v_isSharedCheck_369_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_lctx_354_);
lean_dec(v___x_347_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_369_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_options_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v_options_358_ = lean_ctor_get(v_toCold_349_, 2);
v___x_359_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
v___x_360_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_354_, v___x_359_);
lean_dec_ref(v_lctx_354_);
v___x_361_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_358_);
v___x_362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_362_, 0, v_env_346_);
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
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_364_);
v___x_366_ = v___x_352_;
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
lean_dec(v___x_347_);
lean_dec_ref(v_env_346_);
lean_dec_ref(v_msgData_339_);
v_a_372_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_348_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_348_);
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
lean_object* v_toCold_395_; lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_env_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_toCold_395_ = lean_ctor_get(v___y_392_, 0);
v_ref_396_ = lean_ctor_get(v___y_392_, 2);
v___x_397_ = lean_st_ref_get(v___y_393_);
v_env_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_env_398_);
lean_dec(v___x_397_);
v___x_399_ = lean_st_ref_get(v___y_391_);
v___x_400_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_390_);
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
lean_object* v_lctx_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_421_; 
v_lctx_405_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_399_, 1);
lean_dec(v_unused_422_);
v___x_407_ = v___x_399_;
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_lctx_405_);
lean_dec(v___x_399_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_options_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_options_409_ = lean_ctor_get(v_toCold_395_, 2);
v___x_410_ = lean_unbox(v_a_401_);
lean_dec(v_a_401_);
v___x_411_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_405_, v___x_410_);
lean_dec_ref(v_lctx_405_);
v___x_412_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_409_);
v___x_413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_413_, 0, v_env_398_);
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
lean_dec_ref(v_env_398_);
lean_dec_ref(v_msg_389_);
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
lean_object* v___x_497_; lean_object* v_lctx_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_563_; 
v___x_497_ = lean_st_ref_get(v_a_493_);
v_lctx_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_497_, 1);
lean_dec(v_unused_564_);
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_563_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_lctx_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_563_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_492_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_554_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_554_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_554_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_554_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___y_508_; lean_object* v___y_522_; lean_object* v___y_537_; uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_503_);
if (v___x_551_ == 0)
{
lean_object* v_letDeclsPure_552_; 
v_letDeclsPure_552_ = lean_ctor_get(v_lctx_498_, 2);
lean_inc_ref(v_letDeclsPure_552_);
v___y_537_ = v_letDeclsPure_552_;
goto v___jp_536_;
}
else
{
lean_object* v_letDeclsImpure_553_; 
v_letDeclsImpure_553_ = lean_ctor_get(v_lctx_498_, 3);
lean_inc_ref(v_letDeclsImpure_553_);
v___y_537_ = v_letDeclsImpure_553_;
goto v___jp_536_;
}
v___jp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_508_, v_fvarId_491_);
lean_dec_ref(v___y_508_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v_val_510_; lean_object* v_type_511_; lean_object* v___x_513_; 
lean_del_object(v___x_500_);
lean_dec(v_fvarId_491_);
v_val_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_509_, 1);
v_type_511_ = lean_ctor_get(v_val_510_, 3);
lean_inc_ref(v_type_511_);
lean_dec(v_val_510_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_type_511_);
v___x_513_ = v___x_505_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_type_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v___x_509_);
lean_del_object(v___x_505_);
v___x_515_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_516_ = l_Lean_MessageData_ofName(v_fvarId_491_);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 7);
lean_ctor_set(v___x_500_, 1, v___x_516_);
lean_ctor_set(v___x_500_, 0, v___x_515_);
v___x_518_ = v___x_500_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_518_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_519_;
}
}
}
v___jp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_522_, v_fvarId_491_);
lean_dec_ref(v___y_522_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_del_object(v___x_500_);
lean_dec_ref(v_lctx_498_);
lean_dec(v_fvarId_491_);
v_val_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_type_528_; lean_object* v___x_530_; 
v_type_528_ = lean_ctor_get(v_val_524_, 2);
lean_inc_ref(v_type_528_);
lean_dec(v_val_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
lean_ctor_set(v___x_526_, 0, v_type_528_);
v___x_530_ = v___x_526_;
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
}
else
{
uint8_t v___x_533_; 
lean_dec(v___x_523_);
v___x_533_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_533_ == 0)
{
lean_object* v_funDeclsPure_534_; 
v_funDeclsPure_534_ = lean_ctor_get(v_lctx_498_, 4);
lean_inc_ref(v_funDeclsPure_534_);
lean_dec_ref(v_lctx_498_);
v___y_508_ = v_funDeclsPure_534_;
goto v___jp_507_;
}
else
{
lean_object* v_funDeclsImpure_535_; 
v_funDeclsImpure_535_ = lean_ctor_get(v_lctx_498_, 5);
lean_inc_ref(v_funDeclsImpure_535_);
lean_dec_ref(v_lctx_498_);
v___y_508_ = v_funDeclsImpure_535_;
goto v___jp_507_;
}
}
}
v___jp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_537_, v_fvarId_491_);
lean_dec_ref(v___y_537_);
if (lean_obj_tag(v___x_538_) == 1)
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_del_object(v___x_500_);
lean_dec_ref(v_lctx_498_);
lean_dec(v_fvarId_491_);
v_val_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_type_543_; lean_object* v___x_545_; 
v_type_543_ = lean_ctor_get(v_val_539_, 2);
lean_inc_ref(v_type_543_);
lean_dec(v_val_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 0);
lean_ctor_set(v___x_541_, 0, v_type_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_type_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
uint8_t v___x_548_; 
lean_dec(v___x_538_);
v___x_548_ = lean_unbox(v_a_503_);
if (v___x_548_ == 0)
{
lean_object* v_paramsPure_549_; 
v_paramsPure_549_ = lean_ctor_get(v_lctx_498_, 0);
lean_inc_ref(v_paramsPure_549_);
v___y_522_ = v_paramsPure_549_;
goto v___jp_521_;
}
else
{
lean_object* v_paramsImpure_550_; 
v_paramsImpure_550_ = lean_ctor_get(v_lctx_498_, 1);
lean_inc_ref(v_paramsImpure_550_);
v___y_522_ = v_paramsImpure_550_;
goto v___jp_521_;
}
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_500_);
lean_dec_ref(v_lctx_498_);
lean_dec(v_fvarId_491_);
v_a_555_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_502_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_502_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Compiler_LCNF_getType(v_fvarId_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_573_, v_a_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_576_, lean_object* v_m_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_576_, v_m_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_m_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_580_, lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_584_, lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_584_, v_a_585_, v_x_586_);
lean_dec(v_x_586_);
lean_dec(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_lctx_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_660_; 
v___x_594_ = lean_st_ref_get(v_a_590_);
v_lctx_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_594_, 1);
lean_dec(v_unused_661_);
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_660_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_lctx_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_660_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_589_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_651_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_651_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_651_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_651_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___y_605_; lean_object* v___y_619_; lean_object* v___y_634_; uint8_t v___x_648_; 
v___x_648_ = lean_unbox(v_a_600_);
if (v___x_648_ == 0)
{
lean_object* v_letDeclsPure_649_; 
v_letDeclsPure_649_ = lean_ctor_get(v_lctx_595_, 2);
lean_inc_ref(v_letDeclsPure_649_);
v___y_634_ = v_letDeclsPure_649_;
goto v___jp_633_;
}
else
{
lean_object* v_letDeclsImpure_650_; 
v_letDeclsImpure_650_ = lean_ctor_get(v_lctx_595_, 3);
lean_inc_ref(v_letDeclsImpure_650_);
v___y_634_ = v_letDeclsImpure_650_;
goto v___jp_633_;
}
v___jp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_605_, v_fvarId_588_);
lean_dec_ref(v___y_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_val_607_; lean_object* v_binderName_608_; lean_object* v___x_610_; 
lean_del_object(v___x_597_);
lean_dec(v_fvarId_588_);
v_val_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_val_607_);
lean_dec_ref_known(v___x_606_, 1);
v_binderName_608_ = lean_ctor_get(v_val_607_, 1);
lean_inc(v_binderName_608_);
lean_dec(v_val_607_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_binderName_608_);
v___x_610_ = v___x_602_;
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
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v___x_606_);
lean_del_object(v___x_602_);
v___x_612_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_613_ = l_Lean_MessageData_ofName(v_fvarId_588_);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 7);
lean_ctor_set(v___x_597_, 1, v___x_613_);
lean_ctor_set(v___x_597_, 0, v___x_612_);
v___x_615_ = v___x_597_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_615_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_616_;
}
}
}
v___jp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_619_, v_fvarId_588_);
lean_dec_ref(v___y_619_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_val_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_602_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec_ref(v_lctx_595_);
lean_dec(v_fvarId_588_);
v_val_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_629_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_val_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_binderName_625_; lean_object* v___x_627_; 
v_binderName_625_ = lean_ctor_get(v_val_621_, 1);
lean_inc(v_binderName_625_);
lean_dec(v_val_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 0);
lean_ctor_set(v___x_623_, 0, v_binderName_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_binderName_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
uint8_t v___x_630_; 
lean_dec(v___x_620_);
v___x_630_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
if (v___x_630_ == 0)
{
lean_object* v_funDeclsPure_631_; 
v_funDeclsPure_631_ = lean_ctor_get(v_lctx_595_, 4);
lean_inc_ref(v_funDeclsPure_631_);
lean_dec_ref(v_lctx_595_);
v___y_605_ = v_funDeclsPure_631_;
goto v___jp_604_;
}
else
{
lean_object* v_funDeclsImpure_632_; 
v_funDeclsImpure_632_ = lean_ctor_get(v_lctx_595_, 5);
lean_inc_ref(v_funDeclsImpure_632_);
lean_dec_ref(v_lctx_595_);
v___y_605_ = v_funDeclsImpure_632_;
goto v___jp_604_;
}
}
}
v___jp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_634_, v_fvarId_588_);
lean_dec_ref(v___y_634_);
if (lean_obj_tag(v___x_635_) == 1)
{
lean_object* v_val_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_644_; 
lean_del_object(v___x_602_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec_ref(v_lctx_595_);
lean_dec(v_fvarId_588_);
v_val_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_644_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_val_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_binderName_640_; lean_object* v___x_642_; 
v_binderName_640_ = lean_ctor_get(v_val_636_, 1);
lean_inc(v_binderName_640_);
lean_dec(v_val_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 0);
lean_ctor_set(v___x_638_, 0, v_binderName_640_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_binderName_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v___x_635_);
v___x_645_ = lean_unbox(v_a_600_);
if (v___x_645_ == 0)
{
lean_object* v_paramsPure_646_; 
v_paramsPure_646_ = lean_ctor_get(v_lctx_595_, 0);
lean_inc_ref(v_paramsPure_646_);
v___y_619_ = v_paramsPure_646_;
goto v___jp_618_;
}
else
{
lean_object* v_paramsImpure_647_; 
v_paramsImpure_647_ = lean_ctor_get(v_lctx_595_, 1);
lean_inc_ref(v_paramsImpure_647_);
v___y_619_ = v_paramsImpure_647_;
goto v___jp_618_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_del_object(v___x_597_);
lean_dec_ref(v_lctx_595_);
lean_dec(v_fvarId_588_);
v_a_652_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_599_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_599_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_669_, lean_object* v_fvarId_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___y_675_; 
v___x_673_ = lean_st_ref_get(v_a_671_);
if (v_pu_669_ == 0)
{
lean_object* v_lctx_678_; lean_object* v_paramsPure_679_; 
v_lctx_678_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_lctx_678_);
lean_dec(v___x_673_);
v_paramsPure_679_ = lean_ctor_get(v_lctx_678_, 0);
lean_inc_ref(v_paramsPure_679_);
lean_dec_ref(v_lctx_678_);
v___y_675_ = v_paramsPure_679_;
goto v___jp_674_;
}
else
{
lean_object* v_lctx_680_; lean_object* v_paramsImpure_681_; 
v_lctx_680_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_lctx_680_);
lean_dec(v___x_673_);
v_paramsImpure_681_ = lean_ctor_get(v_lctx_680_, 1);
lean_inc_ref(v_paramsImpure_681_);
lean_dec_ref(v_lctx_680_);
v___y_675_ = v_paramsImpure_681_;
goto v___jp_674_;
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_675_, v_fvarId_670_);
lean_dec_ref(v___y_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_682_, lean_object* v_fvarId_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_pu_boxed_686_; lean_object* v_res_687_; 
v_pu_boxed_686_ = lean_unbox(v_pu_682_);
v_res_687_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_686_, v_fvarId_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec(v_fvarId_683_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_688_, lean_object* v_fvarId_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_688_, v_fvarId_689_, v_a_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_696_, lean_object* v_fvarId_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
uint8_t v_pu_boxed_703_; lean_object* v_res_704_; 
v_pu_boxed_703_ = lean_unbox(v_pu_696_);
v_res_704_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_703_, v_fvarId_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_fvarId_697_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_705_, lean_object* v_fvarId_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; lean_object* v___y_711_; 
v___x_709_ = lean_st_ref_get(v_a_707_);
if (v_pu_705_ == 0)
{
lean_object* v_lctx_714_; lean_object* v_letDeclsPure_715_; 
v_lctx_714_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_lctx_714_);
lean_dec(v___x_709_);
v_letDeclsPure_715_ = lean_ctor_get(v_lctx_714_, 2);
lean_inc_ref(v_letDeclsPure_715_);
lean_dec_ref(v_lctx_714_);
v___y_711_ = v_letDeclsPure_715_;
goto v___jp_710_;
}
else
{
lean_object* v_lctx_716_; lean_object* v_letDeclsImpure_717_; 
v_lctx_716_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_lctx_716_);
lean_dec(v___x_709_);
v_letDeclsImpure_717_ = lean_ctor_get(v_lctx_716_, 3);
lean_inc_ref(v_letDeclsImpure_717_);
lean_dec_ref(v_lctx_716_);
v___y_711_ = v_letDeclsImpure_717_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_711_, v_fvarId_706_);
lean_dec_ref(v___y_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_718_, lean_object* v_fvarId_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v_pu_boxed_722_; lean_object* v_res_723_; 
v_pu_boxed_722_ = lean_unbox(v_pu_718_);
v_res_723_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_722_, v_fvarId_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec(v_fvarId_719_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_724_, lean_object* v_fvarId_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_724_, v_fvarId_725_, v_a_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_732_, lean_object* v_fvarId_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
uint8_t v_pu_boxed_739_; lean_object* v_res_740_; 
v_pu_boxed_739_ = lean_unbox(v_pu_732_);
v_res_740_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_739_, v_fvarId_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_fvarId_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_741_, lean_object* v_fvarId_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___y_747_; 
v___x_745_ = lean_st_ref_get(v_a_743_);
if (v_pu_741_ == 0)
{
lean_object* v_lctx_750_; lean_object* v_funDeclsPure_751_; 
v_lctx_750_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_lctx_750_);
lean_dec(v___x_745_);
v_funDeclsPure_751_ = lean_ctor_get(v_lctx_750_, 4);
lean_inc_ref(v_funDeclsPure_751_);
lean_dec_ref(v_lctx_750_);
v___y_747_ = v_funDeclsPure_751_;
goto v___jp_746_;
}
else
{
lean_object* v_lctx_752_; lean_object* v_funDeclsImpure_753_; 
v_lctx_752_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_lctx_752_);
lean_dec(v___x_745_);
v_funDeclsImpure_753_ = lean_ctor_get(v_lctx_752_, 5);
lean_inc_ref(v_funDeclsImpure_753_);
lean_dec_ref(v_lctx_752_);
v___y_747_ = v_funDeclsImpure_753_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_747_, v_fvarId_742_);
lean_dec_ref(v___y_747_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_754_, lean_object* v_fvarId_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
uint8_t v_pu_boxed_758_; lean_object* v_res_759_; 
v_pu_boxed_758_ = lean_unbox(v_pu_754_);
v_res_759_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_758_, v_fvarId_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec(v_fvarId_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_760_, lean_object* v_fvarId_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_760_, v_fvarId_761_, v_a_763_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_768_, lean_object* v_fvarId_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
uint8_t v_pu_boxed_775_; lean_object* v_res_776_; 
v_pu_boxed_775_ = lean_unbox(v_pu_768_);
v_res_776_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_775_, v_fvarId_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_fvarId_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_777_, lean_object* v_fvarId_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_802_; 
v___x_781_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_777_, v_fvarId_778_, v_a_779_);
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_802_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_802_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_802_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
if (lean_obj_tag(v_a_782_) == 1)
{
lean_object* v_val_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_797_; 
v_val_786_ = lean_ctor_get(v_a_782_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_788_ = v_a_782_;
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_val_786_);
lean_dec(v_a_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_value_790_; lean_object* v___x_792_; 
v_value_790_ = lean_ctor_get(v_val_786_, 3);
lean_inc(v_value_790_);
lean_dec(v_val_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_value_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_value_790_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_792_);
v___x_794_ = v___x_784_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_a_782_);
v___x_798_ = lean_box(0);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_798_);
v___x_800_ = v___x_784_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_803_, lean_object* v_fvarId_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
uint8_t v_pu_boxed_807_; lean_object* v_res_808_; 
v_pu_boxed_807_ = lean_unbox(v_pu_803_);
v_res_808_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_807_, v_fvarId_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec(v_fvarId_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_809_, lean_object* v_fvarId_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_809_, v_fvarId_810_, v_a_812_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_817_, lean_object* v_fvarId_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
uint8_t v_pu_boxed_824_; lean_object* v_res_825_; 
v_pu_boxed_824_ = lean_unbox(v_pu_817_);
v_res_825_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_824_, v_fvarId_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_fvarId_818_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_834_ = 0;
v___x_835_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_834_, v_fvarId_826_, v_a_827_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_863_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_863_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_863_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_863_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
if (lean_obj_tag(v_a_836_) == 1)
{
lean_object* v_val_840_; 
v_val_840_ = lean_ctor_get(v_a_836_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v_a_836_, 1);
if (lean_obj_tag(v_val_840_) == 3)
{
lean_object* v_declName_841_; lean_object* v___x_842_; lean_object* v_env_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
v_declName_841_ = lean_ctor_get(v_val_840_, 0);
lean_inc(v_declName_841_);
lean_dec_ref_known(v_val_840_, 3);
v___x_842_ = lean_st_ref_get(v_a_828_);
v_env_849_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_849_);
lean_dec(v___x_842_);
v___x_850_ = 0;
v___x_851_ = l_Lean_Environment_find_x3f(v_env_849_, v_declName_841_, v___x_850_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_object* v_val_852_; 
v_val_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v___x_851_, 1);
if (lean_obj_tag(v_val_852_) == 6)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
lean_del_object(v___x_838_);
v_isSharedCheck_861_ = !lean_is_exclusive(v_val_852_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_val_852_, 0);
lean_dec(v_unused_862_);
v___x_854_ = v_val_852_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_dec(v_val_852_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = 1;
v___x_857_ = lean_box(v___x_856_);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 0);
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_dec(v_val_852_);
goto v___jp_843_;
}
}
else
{
lean_dec(v___x_851_);
goto v___jp_843_;
}
v___jp_843_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = 0;
v___x_845_ = lean_box(v___x_844_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_845_);
v___x_847_ = v___x_838_;
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
else
{
lean_dec(v_val_840_);
lean_del_object(v___x_838_);
goto v___jp_830_;
}
}
else
{
lean_del_object(v___x_838_);
lean_dec(v_a_836_);
goto v___jp_830_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_835_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_835_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
v___jp_830_:
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = 0;
v___x_832_ = lean_box(v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_fvarId_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_877_, v_a_879_, v_a_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_fvarId_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
if (lean_obj_tag(v_arg_891_) == 1)
{
lean_object* v_fvarId_895_; lean_object* v___x_896_; 
v_fvarId_895_ = lean_ctor_get(v_arg_891_, 0);
v___x_896_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_895_, v_a_892_, v_a_893_);
return v___x_896_;
}
else
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = 0;
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
lean_dec(v_arg_900_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_905_, lean_object* v_arg_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_906_, v_a_908_, v_a_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_913_, lean_object* v_arg_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_pu_boxed_920_; lean_object* v_res_921_; 
v_pu_boxed_920_ = lean_unbox(v_pu_913_);
v_res_921_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_920_, v_arg_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_arg_914_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_925_, lean_object* v_fvarId_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_945_; 
v___x_932_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_925_, v_fvarId_926_, v_a_928_);
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_945_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_945_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_945_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_937_; lean_object* v___x_939_; 
lean_dec(v_fvarId_926_);
v_val_937_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_a_933_, 1);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_val_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_val_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_935_);
lean_dec(v_a_933_);
v___x_941_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_942_ = l_Lean_MessageData_ofName(v_fvarId_926_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_943_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_946_, lean_object* v_fvarId_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_pu_boxed_953_; lean_object* v_res_954_; 
v_pu_boxed_953_ = lean_unbox(v_pu_946_);
v_res_954_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_953_, v_fvarId_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_954_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_958_, lean_object* v_fvarId_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_978_; 
v___x_965_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_958_, v_fvarId_959_, v_a_961_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
if (lean_obj_tag(v_a_966_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_972_; 
lean_dec(v_fvarId_959_);
v_val_970_ = lean_ctor_get(v_a_966_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v_a_966_, 1);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_val_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_val_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_del_object(v___x_968_);
lean_dec(v_a_966_);
v___x_974_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_975_ = l_Lean_MessageData_ofName(v_fvarId_959_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_976_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_979_, lean_object* v_fvarId_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_pu_boxed_986_; lean_object* v_res_987_; 
v_pu_boxed_986_ = lean_unbox(v_pu_979_);
v_res_987_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_986_, v_fvarId_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_991_, lean_object* v_fvarId_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1011_; 
v___x_998_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_991_, v_fvarId_992_, v_a_994_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
if (lean_obj_tag(v_a_999_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1005_; 
lean_dec(v_fvarId_992_);
v_val_1003_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v_a_999_, 1);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_val_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_val_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_del_object(v___x_1001_);
lean_dec(v_a_999_);
v___x_1007_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1008_ = l_Lean_MessageData_ofName(v_fvarId_992_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1009_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1012_, lean_object* v_fvarId_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_pu_boxed_1019_; lean_object* v_res_1020_; 
v_pu_boxed_1019_ = lean_unbox(v_pu_1012_);
v_res_1020_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1019_, v_fvarId_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v_lctx_1025_; lean_object* v_nextIdx_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1037_; 
v___x_1024_ = lean_st_ref_take(v_a_1022_);
v_lctx_1025_ = lean_ctor_get(v___x_1024_, 0);
v_nextIdx_1026_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_nextIdx_1026_);
lean_inc(v_lctx_1025_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_apply_1(v_f_1021_, v_lctx_1025_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_nextIdx_1026_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_st_ref_put(v_a_1022_, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1030_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1038_, v_a_1039_);
lean_dec(v_a_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v_lctx_1049_; lean_object* v_nextIdx_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1061_; 
v___x_1048_ = lean_st_ref_take(v_a_1044_);
v_lctx_1049_ = lean_ctor_get(v___x_1048_, 0);
v_nextIdx_1050_ = lean_ctor_get(v___x_1048_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1052_ = v___x_1048_;
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_nextIdx_1050_);
lean_inc(v_lctx_1049_);
lean_dec(v___x_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_apply_1(v_f_1042_, v_lctx_1049_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_nextIdx_1050_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_st_ref_put(v_a_1044_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1054_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1069_, lean_object* v_decl_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_lctx_1074_; lean_object* v_nextIdx_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1086_; 
v___x_1073_ = lean_st_ref_take(v_a_1071_);
v_lctx_1074_ = lean_ctor_get(v___x_1073_, 0);
v_nextIdx_1075_ = lean_ctor_get(v___x_1073_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1077_ = v___x_1073_;
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_nextIdx_1075_);
lean_inc(v_lctx_1074_);
lean_dec(v___x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1069_, v_lctx_1074_, v_decl_1070_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1080_);
v___x_1082_ = v___x_1077_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_nextIdx_1075_);
v___x_1082_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_st_ref_put(v_a_1071_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1079_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1087_, lean_object* v_decl_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
uint8_t v_pu_boxed_1091_; lean_object* v_res_1092_; 
v_pu_boxed_1091_ = lean_unbox(v_pu_1087_);
v_res_1092_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1091_, v_decl_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_decl_1088_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1093_, lean_object* v_decl_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1093_, v_decl_1094_, v_a_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1101_, lean_object* v_decl_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
uint8_t v_pu_boxed_1108_; lean_object* v_res_1109_; 
v_pu_boxed_1108_ = lean_unbox(v_pu_1101_);
v_res_1109_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1108_, v_decl_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_decl_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1110_, lean_object* v_decl_1111_, uint8_t v_recursive_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_lctx_1116_; lean_object* v_nextIdx_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1128_; 
v___x_1115_ = lean_st_ref_take(v_a_1113_);
v_lctx_1116_ = lean_ctor_get(v___x_1115_, 0);
v_nextIdx_1117_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1119_ = v___x_1115_;
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_nextIdx_1117_);
lean_inc(v_lctx_1116_);
lean_dec(v___x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1110_, v_lctx_1116_, v_decl_1111_, v_recursive_1112_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1122_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_nextIdx_1117_);
v___x_1124_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_st_ref_put(v_a_1113_, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1121_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1129_, lean_object* v_decl_1130_, lean_object* v_recursive_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v_pu_boxed_1134_; uint8_t v_recursive_boxed_1135_; lean_object* v_res_1136_; 
v_pu_boxed_1134_ = lean_unbox(v_pu_1129_);
v_recursive_boxed_1135_ = lean_unbox(v_recursive_1131_);
v_res_1136_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1134_, v_decl_1130_, v_recursive_boxed_1135_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_decl_1130_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1137_, lean_object* v_decl_1138_, uint8_t v_recursive_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1137_, v_decl_1138_, v_recursive_1139_, v_a_1141_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1146_, lean_object* v_decl_1147_, lean_object* v_recursive_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
uint8_t v_pu_boxed_1154_; uint8_t v_recursive_boxed_1155_; lean_object* v_res_1156_; 
v_pu_boxed_1154_ = lean_unbox(v_pu_1146_);
v_recursive_boxed_1155_ = lean_unbox(v_recursive_1148_);
v_res_1156_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1154_, v_decl_1147_, v_recursive_boxed_1155_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_decl_1147_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1157_, lean_object* v_code_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v_lctx_1162_; lean_object* v_nextIdx_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1174_; 
v___x_1161_ = lean_st_ref_take(v_a_1159_);
v_lctx_1162_ = lean_ctor_get(v___x_1161_, 0);
v_nextIdx_1163_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1165_ = v___x_1161_;
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_nextIdx_1163_);
lean_inc(v_lctx_1162_);
lean_dec(v___x_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1157_, v_code_1158_, v_lctx_1162_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_nextIdx_1163_);
v___x_1170_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_st_ref_put(v_a_1159_, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1167_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1175_, lean_object* v_code_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_pu_boxed_1179_; lean_object* v_res_1180_; 
v_pu_boxed_1179_ = lean_unbox(v_pu_1175_);
v_res_1180_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1179_, v_code_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_code_1176_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1181_, lean_object* v_code_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1181_, v_code_1182_, v_a_1184_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1189_, lean_object* v_code_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
uint8_t v_pu_boxed_1196_; lean_object* v_res_1197_; 
v_pu_boxed_1196_ = lean_unbox(v_pu_1189_);
v_res_1197_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1196_, v_code_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec_ref(v_code_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1198_, lean_object* v_param_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1202_; lean_object* v_lctx_1203_; lean_object* v_nextIdx_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1215_; 
v___x_1202_ = lean_st_ref_take(v_a_1200_);
v_lctx_1203_ = lean_ctor_get(v___x_1202_, 0);
v_nextIdx_1204_ = lean_ctor_get(v___x_1202_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1206_ = v___x_1202_;
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_nextIdx_1204_);
lean_inc(v_lctx_1203_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1198_, v_lctx_1203_, v_param_1199_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_nextIdx_1204_);
v___x_1211_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_st_ref_put(v_a_1200_, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1208_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1216_, lean_object* v_param_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
uint8_t v_pu_boxed_1220_; lean_object* v_res_1221_; 
v_pu_boxed_1220_ = lean_unbox(v_pu_1216_);
v_res_1221_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1220_, v_param_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_param_1217_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1222_, lean_object* v_param_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1222_, v_param_1223_, v_a_1225_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1230_, lean_object* v_param_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
uint8_t v_pu_boxed_1237_; lean_object* v_res_1238_; 
v_pu_boxed_1237_ = lean_unbox(v_pu_1230_);
v_res_1238_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1237_, v_param_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_param_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1239_, lean_object* v_params_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_lctx_1244_; lean_object* v_nextIdx_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1256_; 
v___x_1243_ = lean_st_ref_take(v_a_1241_);
v_lctx_1244_ = lean_ctor_get(v___x_1243_, 0);
v_nextIdx_1245_ = lean_ctor_get(v___x_1243_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1247_ = v___x_1243_;
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_nextIdx_1245_);
lean_inc(v_lctx_1244_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1239_, v_lctx_1244_, v_params_1240_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_nextIdx_1245_);
v___x_1252_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_st_ref_put(v_a_1241_, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1249_);
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1257_, lean_object* v_params_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
uint8_t v_pu_boxed_1261_; lean_object* v_res_1262_; 
v_pu_boxed_1261_ = lean_unbox(v_pu_1257_);
v_res_1262_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1261_, v_params_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_params_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1263_, lean_object* v_params_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1263_, v_params_1264_, v_a_1266_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1271_, lean_object* v_params_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
uint8_t v_pu_boxed_1278_; lean_object* v_res_1279_; 
v_pu_boxed_1278_ = lean_unbox(v_pu_1271_);
v_res_1279_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1278_, v_params_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_params_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1280_, lean_object* v_decl_1281_, lean_object* v_a_1282_){
_start:
{
switch(lean_obj_tag(v_decl_1281_))
{
case 0:
{
lean_object* v_decl_1284_; lean_object* v___x_1285_; 
v_decl_1284_ = lean_ctor_get(v_decl_1281_, 0);
v___x_1285_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1280_, v_decl_1284_, v_a_1282_);
return v___x_1285_;
}
case 1:
{
lean_object* v_decl_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; 
v_decl_1286_ = lean_ctor_get(v_decl_1281_, 0);
v___x_1287_ = 1;
v___x_1288_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1280_, v_decl_1286_, v___x_1287_, v_a_1282_);
return v___x_1288_;
}
case 2:
{
lean_object* v_decl_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; 
v_decl_1289_ = lean_ctor_get(v_decl_1281_, 0);
v___x_1290_ = 1;
v___x_1291_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1280_, v_decl_1289_, v___x_1290_, v_a_1282_);
return v___x_1291_;
}
default: 
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1294_, lean_object* v_decl_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
uint8_t v_pu_boxed_1298_; lean_object* v_res_1299_; 
v_pu_boxed_1298_ = lean_unbox(v_pu_1294_);
v_res_1299_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1298_, v_decl_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_decl_1295_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1300_, lean_object* v_decl_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1300_, v_decl_1301_, v_a_1303_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1308_, lean_object* v_decl_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_pu_boxed_1315_; lean_object* v_res_1316_; 
v_pu_boxed_1315_ = lean_unbox(v_pu_1308_);
v_res_1316_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1315_, v_decl_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_decl_1309_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1317_, lean_object* v_as_1318_, size_t v_i_1319_, size_t v_stop_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_eq(v_i_1319_, v_stop_1320_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_array_uget_borrowed(v_as_1318_, v_i_1319_);
v___x_1326_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1317_, v___x_1325_, v___y_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; size_t v___x_1328_; size_t v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_i_1319_, v___x_1328_);
v_i_1319_ = v___x_1329_;
v_b_1321_ = v_a_1327_;
goto _start;
}
else
{
return v___x_1326_;
}
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_b_1321_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1332_, lean_object* v_as_1333_, lean_object* v_i_1334_, lean_object* v_stop_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_pu_boxed_1339_; size_t v_i_boxed_1340_; size_t v_stop_boxed_1341_; lean_object* v_res_1342_; 
v_pu_boxed_1339_ = lean_unbox(v_pu_1332_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_stop_boxed_1341_ = lean_unbox_usize(v_stop_1335_);
lean_dec(v_stop_1335_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1339_, v_as_1333_, v_i_boxed_1340_, v_stop_boxed_1341_, v_b_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v_as_1333_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1343_, lean_object* v_decls_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_decls_1344_);
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
return v___x_1354_;
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_nat_dec_le(v___x_1351_, v___x_1351_);
if (v___x_1355_ == 0)
{
if (v___x_1353_ == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1352_);
return v___x_1356_;
}
else
{
size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = lean_usize_of_nat(v___x_1351_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1343_, v_decls_1344_, v___x_1357_, v___x_1358_, v___x_1352_, v_a_1346_);
return v___x_1359_;
}
}
else
{
size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = lean_usize_of_nat(v___x_1351_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1343_, v_decls_1344_, v___x_1360_, v___x_1361_, v___x_1352_, v_a_1346_);
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1363_, lean_object* v_decls_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
uint8_t v_pu_boxed_1370_; lean_object* v_res_1371_; 
v_pu_boxed_1370_ = lean_unbox(v_pu_1363_);
v_res_1371_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1370_, v_decls_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec_ref(v_decls_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1372_, lean_object* v_as_1373_, size_t v_i_1374_, size_t v_stop_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1372_, v_as_1373_, v_i_1374_, v_stop_1375_, v_b_1376_, v___y_1378_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1383_, lean_object* v_as_1384_, lean_object* v_i_1385_, lean_object* v_stop_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_pu_boxed_1393_; size_t v_i_boxed_1394_; size_t v_stop_boxed_1395_; lean_object* v_res_1396_; 
v_pu_boxed_1393_ = lean_unbox(v_pu_1383_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1385_);
lean_dec(v_i_1385_);
v_stop_boxed_1395_ = lean_unbox_usize(v_stop_1386_);
lean_dec(v_stop_1386_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1393_, v_as_1384_, v_i_boxed_1394_, v_stop_boxed_1395_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_as_1384_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1397_, lean_object* v_v_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
if (lean_obj_tag(v_v_1398_) == 0)
{
lean_object* v_code_1404_; lean_object* v___x_1405_; 
v_code_1404_ = lean_ctor_get(v_v_1398_, 0);
lean_inc_ref(v_code_1404_);
lean_dec_ref_known(v_v_1398_, 1);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_1405_ = lean_apply_6(v_f_1397_, v_code_1404_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, lean_box(0));
return v___x_1405_;
}
else
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_f_1397_);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_v_1398_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_v_1398_, 0);
lean_dec(v_unused_1414_);
v___x_1407_ = v_v_1398_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_v_1398_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = lean_box(0);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1415_, lean_object* v_v_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1415_, v_v_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1423_, lean_object* v_f_1424_, lean_object* v_v_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1424_, v_v_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1432_, lean_object* v_f_1433_, lean_object* v_v_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v_pu_boxed_1440_; lean_object* v_res_1441_; 
v_pu_boxed_1440_ = lean_unbox(v_pu_1432_);
v_res_1441_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1440_, v_f_1433_, v_v_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1442_, lean_object* v_decl_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_toSignature_1449_; lean_object* v_value_1450_; lean_object* v_params_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_toSignature_1449_ = lean_ctor_get(v_decl_1443_, 0);
lean_inc_ref(v_toSignature_1449_);
v_value_1450_ = lean_ctor_get(v_decl_1443_, 1);
lean_inc_ref(v_value_1450_);
lean_dec_ref(v_decl_1443_);
v_params_1451_ = lean_ctor_get(v_toSignature_1449_, 3);
lean_inc_ref(v_params_1451_);
lean_dec_ref(v_toSignature_1449_);
v___x_1452_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1442_, v_params_1451_, v_a_1445_);
lean_dec_ref(v_params_1451_);
lean_dec_ref(v___x_1452_);
v___x_1453_ = lean_box(v_pu_1442_);
v___x_1454_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1454_, 0, v___x_1453_);
v___x_1455_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1454_, v_value_1450_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1456_, lean_object* v_decl_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
uint8_t v_pu_boxed_1463_; lean_object* v_res_1464_; 
v_pu_boxed_1463_ = lean_unbox(v_pu_1456_);
v_res_1464_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1463_, v_decl_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1465_, lean_object* v_decl_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1465_, v_decl_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1473_, lean_object* v_decl_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
uint8_t v_pu_boxed_1480_; lean_object* v_res_1481_; 
v_pu_boxed_1480_ = lean_unbox(v_pu_1473_);
v_res_1481_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1480_, v_decl_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Lean_instInhabitedExpr;
v___x_1484_ = lean_panic_fn_borrowed(v___x_1483_, v_msg_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1489_ = lean_unsigned_to_nat(20u);
v___x_1490_ = lean_unsigned_to_nat(215u);
v___x_1491_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1492_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1493_ = l_mkPanicMessageWithDecl(v___x_1492_, v___x_1491_, v___x_1490_, v___x_1489_, v___x_1488_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1494_, lean_object* v_s_1495_, uint8_t v_translator_1496_, lean_object* v_e_1497_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_Expr_hasFVar(v_e_1497_);
if (v___x_1498_ == 0)
{
return v_e_1497_;
}
else
{
switch(lean_obj_tag(v_e_1497_))
{
case 1:
{
lean_object* v_fvarId_1499_; lean_object* v___x_1500_; 
v_fvarId_1499_ = lean_ctor_get(v_e_1497_, 0);
v___x_1500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1495_, v_fvarId_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
return v_e_1497_;
}
else
{
lean_object* v_val_1501_; 
lean_dec_ref_known(v_e_1497_, 1);
v_val_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___x_1500_, 1);
switch(lean_obj_tag(v_val_1501_))
{
case 0:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1502_;
}
case 1:
{
if (v_translator_1496_ == 0)
{
lean_object* v_fvarId_1503_; lean_object* v___x_1504_; 
v_fvarId_1503_ = lean_ctor_get(v_val_1501_, 0);
lean_inc(v_fvarId_1503_);
lean_dec_ref_known(v_val_1501_, 1);
v___x_1504_ = l_Lean_Expr_fvar___override(v_fvarId_1503_);
v_e_1497_ = v___x_1504_;
goto _start;
}
else
{
lean_object* v_fvarId_1506_; lean_object* v___x_1507_; 
v_fvarId_1506_ = lean_ctor_get(v_val_1501_, 0);
lean_inc(v_fvarId_1506_);
lean_dec_ref_known(v_val_1501_, 1);
v___x_1507_ = l_Lean_Expr_fvar___override(v_fvarId_1506_);
return v___x_1507_;
}
}
default: 
{
if (v_translator_1496_ == 0)
{
lean_object* v_expr_1508_; 
v_expr_1508_ = lean_ctor_get(v_val_1501_, 0);
lean_inc_ref(v_expr_1508_);
lean_dec_ref_known(v_val_1501_, 1);
v_e_1497_ = v_expr_1508_;
goto _start;
}
else
{
lean_object* v_expr_1510_; 
v_expr_1510_ = lean_ctor_get(v_val_1501_, 0);
lean_inc_ref(v_expr_1510_);
lean_dec_ref_known(v_val_1501_, 1);
return v_expr_1510_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1511_; lean_object* v_arg_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v_fn_1511_ = lean_ctor_get(v_e_1497_, 0);
v_arg_1512_ = lean_ctor_get(v_e_1497_, 1);
lean_inc_ref(v_fn_1511_);
v___x_1513_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1494_, v_s_1495_, v_translator_1496_, v_fn_1511_);
lean_inc_ref(v_arg_1512_);
v___x_1514_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_arg_1512_);
v___x_1515_ = lean_ptr_addr(v_fn_1511_);
v___x_1516_ = lean_ptr_addr(v___x_1513_);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref_known(v_e_1497_, 2);
v___x_1518_ = l_Lean_Expr_app___override(v___x_1513_, v___x_1514_);
v___x_1519_ = l_Lean_Expr_headBeta(v___x_1518_);
return v___x_1519_;
}
else
{
size_t v___x_1520_; size_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_ptr_addr(v_arg_1512_);
v___x_1521_ = lean_ptr_addr(v___x_1514_);
v___x_1522_ = lean_usize_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref_known(v_e_1497_, 2);
v___x_1523_ = l_Lean_Expr_app___override(v___x_1513_, v___x_1514_);
v___x_1524_ = l_Lean_Expr_headBeta(v___x_1523_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; 
lean_dec_ref(v___x_1514_);
lean_dec_ref(v___x_1513_);
v___x_1525_ = l_Lean_Expr_headBeta(v_e_1497_);
return v___x_1525_;
}
}
}
case 6:
{
lean_object* v_binderName_1526_; lean_object* v_binderType_1527_; lean_object* v_body_1528_; uint8_t v_binderInfo_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; size_t v___x_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v_binderName_1526_ = lean_ctor_get(v_e_1497_, 0);
v_binderType_1527_ = lean_ctor_get(v_e_1497_, 1);
v_body_1528_ = lean_ctor_get(v_e_1497_, 2);
v_binderInfo_1529_ = lean_ctor_get_uint8(v_e_1497_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1527_);
v___x_1530_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_binderType_1527_);
lean_inc_ref(v_body_1528_);
v___x_1531_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_body_1528_);
v___x_1532_ = lean_ptr_addr(v_binderType_1527_);
v___x_1533_ = lean_ptr_addr(v___x_1530_);
v___x_1534_ = lean_usize_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_binderName_1526_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1535_ = l_Lean_Expr_lam___override(v_binderName_1526_, v___x_1530_, v___x_1531_, v_binderInfo_1529_);
return v___x_1535_;
}
else
{
size_t v___x_1536_; size_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_ptr_addr(v_body_1528_);
v___x_1537_ = lean_ptr_addr(v___x_1531_);
v___x_1538_ = lean_usize_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_inc(v_binderName_1526_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1539_ = l_Lean_Expr_lam___override(v_binderName_1526_, v___x_1530_, v___x_1531_, v_binderInfo_1529_);
return v___x_1539_;
}
else
{
uint8_t v___x_1540_; 
v___x_1540_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1529_, v_binderInfo_1529_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_inc(v_binderName_1526_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1541_ = l_Lean_Expr_lam___override(v_binderName_1526_, v___x_1530_, v___x_1531_, v_binderInfo_1529_);
return v___x_1541_;
}
else
{
lean_dec_ref(v___x_1531_);
lean_dec_ref(v___x_1530_);
return v_e_1497_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1542_; lean_object* v_binderType_1543_; lean_object* v_body_1544_; uint8_t v_binderInfo_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; uint8_t v___x_1550_; 
v_binderName_1542_ = lean_ctor_get(v_e_1497_, 0);
v_binderType_1543_ = lean_ctor_get(v_e_1497_, 1);
v_body_1544_ = lean_ctor_get(v_e_1497_, 2);
v_binderInfo_1545_ = lean_ctor_get_uint8(v_e_1497_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1543_);
v___x_1546_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_binderType_1543_);
lean_inc_ref(v_body_1544_);
v___x_1547_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_body_1544_);
v___x_1548_ = lean_ptr_addr(v_binderType_1543_);
v___x_1549_ = lean_ptr_addr(v___x_1546_);
v___x_1550_ = lean_usize_dec_eq(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_inc(v_binderName_1542_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1551_ = l_Lean_Expr_forallE___override(v_binderName_1542_, v___x_1546_, v___x_1547_, v_binderInfo_1545_);
return v___x_1551_;
}
else
{
size_t v___x_1552_; size_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = lean_ptr_addr(v_body_1544_);
v___x_1553_ = lean_ptr_addr(v___x_1547_);
v___x_1554_ = lean_usize_dec_eq(v___x_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_inc(v_binderName_1542_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1555_ = l_Lean_Expr_forallE___override(v_binderName_1542_, v___x_1546_, v___x_1547_, v_binderInfo_1545_);
return v___x_1555_;
}
else
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1545_, v_binderInfo_1545_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_inc(v_binderName_1542_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1557_ = l_Lean_Expr_forallE___override(v_binderName_1542_, v___x_1546_, v___x_1547_, v_binderInfo_1545_);
return v___x_1557_;
}
else
{
lean_dec_ref(v___x_1547_);
lean_dec_ref(v___x_1546_);
return v_e_1497_;
}
}
}
}
case 8:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref_known(v_e_1497_, 4);
v___x_1558_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1559_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1558_);
return v___x_1559_;
}
case 10:
{
lean_object* v_data_1560_; lean_object* v_expr_1561_; lean_object* v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; uint8_t v___x_1565_; 
v_data_1560_ = lean_ctor_get(v_e_1497_, 0);
v_expr_1561_ = lean_ctor_get(v_e_1497_, 1);
lean_inc_ref(v_expr_1561_);
v___x_1562_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_expr_1561_);
v___x_1563_ = lean_ptr_addr(v_expr_1561_);
v___x_1564_ = lean_ptr_addr(v___x_1562_);
v___x_1565_ = lean_usize_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_inc(v_data_1560_);
lean_dec_ref_known(v_e_1497_, 2);
v___x_1566_ = l_Lean_Expr_mdata___override(v_data_1560_, v___x_1562_);
return v___x_1566_;
}
else
{
lean_dec_ref(v___x_1562_);
return v_e_1497_;
}
}
case 11:
{
lean_object* v_typeName_1567_; lean_object* v_idx_1568_; lean_object* v_struct_1569_; lean_object* v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; uint8_t v___x_1573_; 
v_typeName_1567_ = lean_ctor_get(v_e_1497_, 0);
v_idx_1568_ = lean_ctor_get(v_e_1497_, 1);
v_struct_1569_ = lean_ctor_get(v_e_1497_, 2);
lean_inc_ref(v_struct_1569_);
v___x_1570_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1494_, v_s_1495_, v_translator_1496_, v_struct_1569_);
v___x_1571_ = lean_ptr_addr(v_struct_1569_);
v___x_1572_ = lean_ptr_addr(v___x_1570_);
v___x_1573_ = lean_usize_dec_eq(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_inc(v_idx_1568_);
lean_inc(v_typeName_1567_);
lean_dec_ref_known(v_e_1497_, 3);
v___x_1574_ = l_Lean_Expr_proj___override(v_typeName_1567_, v_idx_1568_, v___x_1570_);
return v___x_1574_;
}
else
{
lean_dec_ref(v___x_1570_);
return v_e_1497_;
}
}
default: 
{
return v_e_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1575_, lean_object* v_s_1576_, uint8_t v_translator_1577_, lean_object* v_e_1578_){
_start:
{
if (lean_obj_tag(v_e_1578_) == 5)
{
lean_object* v_fn_1579_; lean_object* v_arg_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; uint8_t v___x_1585_; 
v_fn_1579_ = lean_ctor_get(v_e_1578_, 0);
v_arg_1580_ = lean_ctor_get(v_e_1578_, 1);
lean_inc_ref(v_fn_1579_);
v___x_1581_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1575_, v_s_1576_, v_translator_1577_, v_fn_1579_);
lean_inc_ref(v_arg_1580_);
v___x_1582_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1575_, v_s_1576_, v_translator_1577_, v_arg_1580_);
v___x_1583_ = lean_ptr_addr(v_fn_1579_);
v___x_1584_ = lean_ptr_addr(v___x_1581_);
v___x_1585_ = lean_usize_dec_eq(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref_known(v_e_1578_, 2);
v___x_1586_ = l_Lean_Expr_app___override(v___x_1581_, v___x_1582_);
return v___x_1586_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_ptr_addr(v_arg_1580_);
v___x_1588_ = lean_ptr_addr(v___x_1582_);
v___x_1589_ = lean_usize_dec_eq(v___x_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref_known(v_e_1578_, 2);
v___x_1590_ = l_Lean_Expr_app___override(v___x_1581_, v___x_1582_);
return v___x_1590_;
}
else
{
lean_dec_ref(v___x_1582_);
lean_dec_ref(v___x_1581_);
return v_e_1578_;
}
}
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1575_, v_s_1576_, v_translator_1577_, v_e_1578_);
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1592_, lean_object* v_s_1593_, lean_object* v_translator_1594_, lean_object* v_e_1595_){
_start:
{
uint8_t v_pu_boxed_1596_; uint8_t v_translator_boxed_1597_; lean_object* v_res_1598_; 
v_pu_boxed_1596_ = lean_unbox(v_pu_1592_);
v_translator_boxed_1597_ = lean_unbox(v_translator_1594_);
v_res_1598_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1596_, v_s_1593_, v_translator_boxed_1597_, v_e_1595_);
lean_dec_ref(v_s_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1599_, lean_object* v_s_1600_, lean_object* v_translator_1601_, lean_object* v_e_1602_){
_start:
{
uint8_t v_pu_boxed_1603_; uint8_t v_translator_boxed_1604_; lean_object* v_res_1605_; 
v_pu_boxed_1603_ = lean_unbox(v_pu_1599_);
v_translator_boxed_1604_ = lean_unbox(v_translator_1601_);
v_res_1605_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1603_, v_s_1600_, v_translator_boxed_1604_, v_e_1602_);
lean_dec_ref(v_s_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1606_, lean_object* v_s_1607_, lean_object* v_e_1608_, uint8_t v_translator_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1606_, v_s_1607_, v_translator_1609_, v_e_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1611_, lean_object* v_s_1612_, lean_object* v_e_1613_, lean_object* v_translator_1614_){
_start:
{
uint8_t v_pu_boxed_1615_; uint8_t v_translator_boxed_1616_; lean_object* v_res_1617_; 
v_pu_boxed_1615_ = lean_unbox(v_pu_1611_);
v_translator_boxed_1616_ = lean_unbox(v_translator_1614_);
v_res_1617_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1615_, v_s_1612_, v_e_1613_, v_translator_boxed_1616_);
lean_dec_ref(v_s_1612_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1618_){
_start:
{
if (lean_obj_tag(v_x_1618_) == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_unsigned_to_nat(1u);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1621_);
lean_dec(v_x_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1623_, lean_object* v_k_1624_){
_start:
{
if (lean_obj_tag(v_t_1623_) == 0)
{
lean_object* v_fvarId_1625_; lean_object* v___x_1626_; 
v_fvarId_1625_ = lean_ctor_get(v_t_1623_, 0);
lean_inc(v_fvarId_1625_);
lean_dec_ref_known(v_t_1623_, 1);
v___x_1626_ = lean_apply_1(v_k_1624_, v_fvarId_1625_);
return v___x_1626_;
}
else
{
return v_k_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1627_, lean_object* v_ctorIdx_1628_, lean_object* v_t_1629_, lean_object* v_h_1630_, lean_object* v_k_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1629_, v_k_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1633_, lean_object* v_ctorIdx_1634_, lean_object* v_t_1635_, lean_object* v_h_1636_, lean_object* v_k_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1633_, v_ctorIdx_1634_, v_t_1635_, v_h_1636_, v_k_1637_);
lean_dec(v_ctorIdx_1634_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1639_, lean_object* v_fvar_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1639_, v_fvar_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_fvar_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1643_, v_fvar_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1647_, lean_object* v_erased_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1647_, v_erased_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_erased_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1651_, v_erased_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1659_, lean_object* v_fvarId_1660_, uint8_t v_translator_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1659_, v_fvarId_1660_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_fvarId_1660_);
return v___x_1663_;
}
else
{
lean_object* v_val_1664_; 
lean_dec(v_fvarId_1660_);
v_val_1664_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v___x_1662_, 1);
if (lean_obj_tag(v_val_1664_) == 1)
{
if (v_translator_1661_ == 0)
{
lean_object* v_fvarId_1665_; 
v_fvarId_1665_ = lean_ctor_get(v_val_1664_, 0);
lean_inc(v_fvarId_1665_);
lean_dec_ref_known(v_val_1664_, 1);
v_fvarId_1660_ = v_fvarId_1665_;
goto _start;
}
else
{
lean_object* v_fvarId_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_fvarId_1667_ = lean_ctor_get(v_val_1664_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_val_1664_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v_val_1664_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_fvarId_1667_);
lean_dec(v_val_1664_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 0);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_fvarId_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_val_1664_);
v___x_1675_ = lean_box(1);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1676_, lean_object* v_fvarId_1677_, lean_object* v_translator_1678_){
_start:
{
uint8_t v_translator_boxed_1679_; lean_object* v_res_1680_; 
v_translator_boxed_1679_ = lean_unbox(v_translator_1678_);
v_res_1680_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1676_, v_fvarId_1677_, v_translator_boxed_1679_);
lean_dec_ref(v_s_1676_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1681_, lean_object* v_s_1682_, lean_object* v_fvarId_1683_, uint8_t v_translator_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1682_, v_fvarId_1683_, v_translator_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1686_, lean_object* v_s_1687_, lean_object* v_fvarId_1688_, lean_object* v_translator_1689_){
_start:
{
uint8_t v_pu_boxed_1690_; uint8_t v_translator_boxed_1691_; lean_object* v_res_1692_; 
v_pu_boxed_1690_ = lean_unbox(v_pu_1686_);
v_translator_boxed_1691_ = lean_unbox(v_translator_1689_);
v_res_1692_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1690_, v_s_1687_, v_fvarId_1688_, v_translator_boxed_1691_);
lean_dec_ref(v_s_1687_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1693_, lean_object* v_s_1694_, lean_object* v_arg_1695_, uint8_t v_translator_1696_){
_start:
{
switch(lean_obj_tag(v_arg_1695_))
{
case 0:
{
return v_arg_1695_;
}
case 1:
{
lean_object* v_fvarId_1697_; lean_object* v___x_1698_; 
v_fvarId_1697_ = lean_ctor_get(v_arg_1695_, 0);
v___x_1698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1694_, v_fvarId_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
return v_arg_1695_;
}
else
{
lean_object* v_val_1699_; 
lean_dec_ref_known(v_arg_1695_, 1);
v_val_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1699_);
lean_dec_ref_known(v___x_1698_, 1);
switch(lean_obj_tag(v_val_1699_))
{
case 0:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_box(0);
return v___x_1700_;
}
case 1:
{
lean_object* v_fvarId_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1709_; 
v_fvarId_1701_ = lean_ctor_get(v_val_1699_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_val_1699_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1703_ = v_val_1699_;
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_fvarId_1701_);
lean_dec(v_val_1699_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_fvarId_1701_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
if (v_translator_1696_ == 0)
{
v_arg_1695_ = v___x_1706_;
goto _start;
}
else
{
return v___x_1706_;
}
}
}
}
default: 
{
lean_object* v_expr_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_expr_1710_ = lean_ctor_get(v_val_1699_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_val_1699_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v_val_1699_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_expr_1710_);
lean_dec(v_val_1699_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_expr_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_expr_1718_ = lean_ctor_get(v_arg_1695_, 0);
lean_inc_ref(v_expr_1718_);
v___x_1719_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1693_, v_s_1694_, v_translator_1696_, v_expr_1718_);
v___x_1720_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1693_, v_arg_1695_, v___x_1719_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1721_, lean_object* v_s_1722_, lean_object* v_arg_1723_, lean_object* v_translator_1724_){
_start:
{
uint8_t v_pu_boxed_1725_; uint8_t v_translator_boxed_1726_; lean_object* v_res_1727_; 
v_pu_boxed_1725_ = lean_unbox(v_pu_1721_);
v_translator_boxed_1726_ = lean_unbox(v_translator_1724_);
v_res_1727_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1725_, v_s_1722_, v_arg_1723_, v_translator_boxed_1726_);
lean_dec_ref(v_s_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1728_, lean_object* v_s_1729_, uint8_t v_translator_1730_, lean_object* v_i_1731_, lean_object* v_as_1732_){
_start:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_array_get_size(v_as_1732_);
v___x_1734_ = lean_nat_dec_lt(v_i_1731_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_dec(v_i_1731_);
return v_as_1732_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; uint8_t v___x_1739_; 
v_a_1735_ = lean_array_fget_borrowed(v_as_1732_, v_i_1731_);
lean_inc(v_a_1735_);
v___x_1736_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1728_, v_s_1729_, v_a_1735_, v_translator_1730_);
v___x_1737_ = lean_ptr_addr(v_a_1735_);
v___x_1738_ = lean_ptr_addr(v___x_1736_);
v___x_1739_ = lean_usize_dec_eq(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_add(v_i_1731_, v___x_1740_);
v___x_1742_ = lean_array_fset(v_as_1732_, v_i_1731_, v___x_1736_);
lean_dec(v_i_1731_);
v_i_1731_ = v___x_1741_;
v_as_1732_ = v___x_1742_;
goto _start;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v___x_1736_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_i_1731_, v___x_1744_);
lean_dec(v_i_1731_);
v_i_1731_ = v___x_1745_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1747_, lean_object* v_s_1748_, lean_object* v_translator_1749_, lean_object* v_i_1750_, lean_object* v_as_1751_){
_start:
{
uint8_t v_pu_boxed_1752_; uint8_t v_translator_boxed_1753_; lean_object* v_res_1754_; 
v_pu_boxed_1752_ = lean_unbox(v_pu_1747_);
v_translator_boxed_1753_ = lean_unbox(v_translator_1749_);
v_res_1754_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1752_, v_s_1748_, v_translator_boxed_1753_, v_i_1750_, v_as_1751_);
lean_dec_ref(v_s_1748_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1755_, lean_object* v_s_1756_, lean_object* v_args_1757_, uint8_t v_translator_1758_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1755_, v_s_1756_, v_translator_1758_, v___x_1759_, v_args_1757_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1761_, lean_object* v_s_1762_, lean_object* v_args_1763_, lean_object* v_translator_1764_){
_start:
{
uint8_t v_pu_boxed_1765_; uint8_t v_translator_boxed_1766_; lean_object* v_res_1767_; 
v_pu_boxed_1765_ = lean_unbox(v_pu_1761_);
v_translator_boxed_1766_ = lean_unbox(v_translator_1764_);
v_res_1767_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1765_, v_s_1762_, v_args_1763_, v_translator_boxed_1766_);
lean_dec_ref(v_s_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1768_, lean_object* v_s_1769_, lean_object* v_e_1770_, uint8_t v_translator_1771_){
_start:
{
lean_object* v_fvarId_1773_; lean_object* v_args_1779_; 
switch(lean_obj_tag(v_e_1770_))
{
case 2:
{
lean_object* v_struct_1782_; lean_object* v___x_1783_; 
v_struct_1782_ = lean_ctor_get(v_e_1770_, 2);
lean_inc(v_struct_1782_);
v___x_1783_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_struct_1782_, v_translator_1771_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_fvarId_1784_; lean_object* v___x_1785_; 
v_fvarId_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_fvarId_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1768_, v_e_1770_, v_fvarId_1784_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v_e_1770_, 3);
v___x_1786_ = lean_box(1);
return v___x_1786_;
}
}
case 3:
{
lean_object* v_args_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_args_1787_ = lean_ctor_get(v_e_1770_, 2);
lean_inc_ref(v_args_1787_);
v___x_1788_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1768_, v_s_1769_, v_args_1787_, v_translator_1771_);
v___x_1789_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1770_, v___x_1788_);
return v___x_1789_;
}
case 4:
{
lean_object* v_fvarId_1790_; lean_object* v_args_1791_; lean_object* v___x_1792_; 
v_fvarId_1790_ = lean_ctor_get(v_e_1770_, 0);
v_args_1791_ = lean_ctor_get(v_e_1770_, 1);
lean_inc(v_fvarId_1790_);
v___x_1792_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_fvarId_1790_, v_translator_1771_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_fvarId_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_fvarId_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_fvarId_1793_);
lean_dec_ref_known(v___x_1792_, 1);
lean_inc_ref(v_args_1791_);
v___x_1794_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1768_, v_s_1769_, v_args_1791_, v_translator_1771_);
v___x_1795_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1770_, v_fvarId_1793_, v___x_1794_);
lean_dec_ref_known(v_e_1770_, 2);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; 
lean_dec_ref_known(v_e_1770_, 2);
v___x_1796_ = lean_box(1);
return v___x_1796_;
}
}
case 5:
{
lean_object* v_args_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_args_1797_ = lean_ctor_get(v_e_1770_, 1);
lean_inc_ref(v_args_1797_);
v___x_1798_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1768_, v_s_1769_, v_args_1797_, v_translator_1771_);
v___x_1799_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1770_, v___x_1798_);
return v___x_1799_;
}
case 6:
{
lean_object* v_var_1800_; 
v_var_1800_ = lean_ctor_get(v_e_1770_, 1);
lean_inc(v_var_1800_);
v_fvarId_1773_ = v_var_1800_;
goto v___jp_1772_;
}
case 7:
{
lean_object* v_var_1801_; 
v_var_1801_ = lean_ctor_get(v_e_1770_, 1);
lean_inc(v_var_1801_);
v_fvarId_1773_ = v_var_1801_;
goto v___jp_1772_;
}
case 8:
{
lean_object* v_var_1802_; lean_object* v___x_1803_; 
v_var_1802_ = lean_ctor_get(v_e_1770_, 2);
lean_inc(v_var_1802_);
v___x_1803_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_var_1802_, v_translator_1771_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_fvarId_1804_; lean_object* v___x_1805_; 
v_fvarId_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_fvarId_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1768_, v_e_1770_, v_fvarId_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
lean_dec_ref_known(v_e_1770_, 3);
v___x_1806_ = lean_box(1);
return v___x_1806_;
}
}
case 9:
{
lean_object* v_args_1807_; 
v_args_1807_ = lean_ctor_get(v_e_1770_, 1);
lean_inc_ref(v_args_1807_);
v_args_1779_ = v_args_1807_;
goto v___jp_1778_;
}
case 10:
{
lean_object* v_args_1808_; 
v_args_1808_ = lean_ctor_get(v_e_1770_, 1);
lean_inc_ref(v_args_1808_);
v_args_1779_ = v_args_1808_;
goto v___jp_1778_;
}
case 11:
{
lean_object* v_n_1809_; lean_object* v_var_1810_; lean_object* v___x_1811_; 
v_n_1809_ = lean_ctor_get(v_e_1770_, 0);
lean_inc(v_n_1809_);
v_var_1810_ = lean_ctor_get(v_e_1770_, 1);
lean_inc(v_var_1810_);
v___x_1811_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_var_1810_, v_translator_1771_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_fvarId_1812_; lean_object* v___x_1813_; 
v_fvarId_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_fvarId_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___x_1813_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1770_, v_n_1809_, v_fvarId_1812_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; 
lean_dec_ref_known(v_e_1770_, 2);
lean_dec(v_n_1809_);
v___x_1814_ = lean_box(1);
return v___x_1814_;
}
}
case 12:
{
lean_object* v_var_1815_; lean_object* v_i_1816_; uint8_t v_updateHeader_1817_; lean_object* v_args_1818_; lean_object* v___x_1819_; 
v_var_1815_ = lean_ctor_get(v_e_1770_, 0);
v_i_1816_ = lean_ctor_get(v_e_1770_, 1);
lean_inc_ref(v_i_1816_);
v_updateHeader_1817_ = lean_ctor_get_uint8(v_e_1770_, sizeof(void*)*3);
v_args_1818_ = lean_ctor_get(v_e_1770_, 2);
lean_inc(v_var_1815_);
v___x_1819_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_var_1815_, v_translator_1771_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_fvarId_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_fvarId_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_fvarId_1820_);
lean_dec_ref_known(v___x_1819_, 1);
lean_inc_ref(v_args_1818_);
v___x_1821_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1768_, v_s_1769_, v_args_1818_, v_translator_1771_);
v___x_1822_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1770_, v_fvarId_1820_, v_i_1816_, v_updateHeader_1817_, v___x_1821_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; 
lean_dec_ref(v_i_1816_);
lean_dec_ref_known(v_e_1770_, 3);
v___x_1823_ = lean_box(1);
return v___x_1823_;
}
}
case 13:
{
lean_object* v_ty_1824_; lean_object* v_fvarId_1825_; lean_object* v___x_1826_; 
v_ty_1824_ = lean_ctor_get(v_e_1770_, 0);
lean_inc_ref(v_ty_1824_);
v_fvarId_1825_ = lean_ctor_get(v_e_1770_, 1);
lean_inc(v_fvarId_1825_);
v___x_1826_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_fvarId_1825_, v_translator_1771_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_fvarId_1827_; lean_object* v___x_1828_; 
v_fvarId_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_fvarId_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1770_, v_ty_1824_, v_fvarId_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; 
lean_dec_ref_known(v_e_1770_, 2);
lean_dec_ref(v_ty_1824_);
v___x_1829_ = lean_box(1);
return v___x_1829_;
}
}
case 14:
{
lean_object* v_fvarId_1830_; lean_object* v___x_1831_; 
v_fvarId_1830_ = lean_ctor_get(v_e_1770_, 0);
lean_inc(v_fvarId_1830_);
v___x_1831_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_fvarId_1830_, v_translator_1771_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_fvarId_1832_; lean_object* v___x_1833_; 
v_fvarId_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_fvarId_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1770_, v_fvarId_1832_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; 
lean_dec_ref_known(v_e_1770_, 1);
v___x_1834_ = lean_box(1);
return v___x_1834_;
}
}
case 15:
{
lean_object* v_fvarId_1835_; lean_object* v___x_1836_; 
v_fvarId_1835_ = lean_ctor_get(v_e_1770_, 0);
lean_inc(v_fvarId_1835_);
v___x_1836_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_fvarId_1835_, v_translator_1771_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_fvarId_1837_; lean_object* v___x_1838_; 
v_fvarId_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_fvarId_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1770_, v_fvarId_1837_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; 
lean_dec_ref_known(v_e_1770_, 1);
v___x_1839_ = lean_box(1);
return v___x_1839_;
}
}
default: 
{
return v_e_1770_;
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1769_, v_fvarId_1773_, v_translator_1771_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_fvarId_1775_; lean_object* v___x_1776_; 
v_fvarId_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_fvarId_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1768_, v_e_1770_, v_fvarId_1775_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
lean_dec(v_e_1770_);
v___x_1777_ = lean_box(1);
return v___x_1777_;
}
}
v___jp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1768_, v_s_1769_, v_args_1779_, v_translator_1771_);
v___x_1781_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1770_, v___x_1780_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1840_, lean_object* v_s_1841_, lean_object* v_e_1842_, lean_object* v_translator_1843_){
_start:
{
uint8_t v_pu_boxed_1844_; uint8_t v_translator_boxed_1845_; lean_object* v_res_1846_; 
v_pu_boxed_1844_ = lean_unbox(v_pu_1840_);
v_translator_boxed_1845_ = lean_unbox(v_translator_1843_);
v_res_1846_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1844_, v_s_1841_, v_e_1842_, v_translator_boxed_1845_);
lean_dec_ref(v_s_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1847_, lean_object* v_inst_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_apply_2(v_inst_1847_, lean_box(0), v_inst_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1850_, uint8_t v_t_1851_, lean_object* v_m_1852_, lean_object* v_n_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_apply_2(v_inst_1854_, lean_box(0), v_inst_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1857_, lean_object* v_t_1858_, lean_object* v_m_1859_, lean_object* v_n_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_){
_start:
{
uint8_t v_pu_boxed_1863_; uint8_t v_t_boxed_1864_; lean_object* v_res_1865_; 
v_pu_boxed_1863_ = lean_unbox(v_pu_1857_);
v_t_boxed_1864_ = lean_unbox(v_t_1858_);
v_res_1865_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1863_, v_t_boxed_1864_, v_m_1859_, v_n_1860_, v_inst_1861_, v_inst_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_f_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_apply_1(v_inst_1866_, v_f_1868_);
v___x_1870_ = lean_apply_2(v_inst_1867_, lean_box(0), v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1871_, lean_object* v_inst_1872_){
_start:
{
lean_object* v___f_1873_; 
v___f_1873_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1873_, 0, v_inst_1872_);
lean_closure_set(v___f_1873_, 1, v_inst_1871_);
return v___f_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1874_, lean_object* v_m_1875_, lean_object* v_n_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_){
_start:
{
lean_object* v___f_1879_; 
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1879_, 0, v_inst_1878_);
lean_closure_set(v___f_1879_, 1, v_inst_1877_);
return v___f_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1880_, lean_object* v_m_1881_, lean_object* v_n_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_){
_start:
{
uint8_t v_pu_boxed_1885_; lean_object* v_res_1886_; 
v_pu_boxed_1885_ = lean_unbox(v_pu_1880_);
v_res_1886_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1885_, v_m_1881_, v_n_1882_, v_inst_1883_, v_inst_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1887_, lean_object* v___x_1888_, lean_object* v_fvarId_1889_, lean_object* v_arg_1890_, lean_object* v_s_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1887_, v___x_1888_, v_s_1891_, v_fvarId_1889_, v_arg_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1895_, lean_object* v_fvarId_1896_, lean_object* v_arg_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; 
v___x_1898_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1899_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1900_, 0, v___x_1898_);
lean_closure_set(v___f_1900_, 1, v___x_1899_);
lean_closure_set(v___f_1900_, 2, v_fvarId_1896_);
lean_closure_set(v___f_1900_, 3, v_arg_1897_);
v___x_1901_ = lean_apply_1(v_inst_1895_, v___f_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1902_, uint8_t v_pu_1903_, lean_object* v_inst_1904_, lean_object* v_fvarId_1905_, lean_object* v_arg_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___f_1909_; lean_object* v___x_1910_; 
v___x_1907_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1908_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1909_, 0, v___x_1907_);
lean_closure_set(v___f_1909_, 1, v___x_1908_);
lean_closure_set(v___f_1909_, 2, v_fvarId_1905_);
lean_closure_set(v___f_1909_, 3, v_arg_1906_);
v___x_1910_ = lean_apply_1(v_inst_1904_, v___f_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1911_, lean_object* v_pu_1912_, lean_object* v_inst_1913_, lean_object* v_fvarId_1914_, lean_object* v_arg_1915_){
_start:
{
uint8_t v_pu_boxed_1916_; lean_object* v_res_1917_; 
v_pu_boxed_1916_ = lean_unbox(v_pu_1912_);
v_res_1917_ = l_Lean_Compiler_LCNF_addSubst(v_m_1911_, v_pu_boxed_1916_, v_inst_1913_, v_fvarId_1914_, v_arg_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1918_, lean_object* v___x_1919_, lean_object* v___x_1920_, lean_object* v_fvarId_1921_, lean_object* v_s_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_fvarId_x27_1918_);
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1919_, v___x_1920_, v_s_1922_, v_fvarId_1921_, v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1925_, lean_object* v_fvarId_1926_, lean_object* v_fvarId_x27_1927_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
v___x_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1930_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1930_, 0, v_fvarId_x27_1927_);
lean_closure_set(v___f_1930_, 1, v___x_1928_);
lean_closure_set(v___f_1930_, 2, v___x_1929_);
lean_closure_set(v___f_1930_, 3, v_fvarId_1926_);
v___x_1931_ = lean_apply_1(v_inst_1925_, v___f_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1932_, uint8_t v_ph_1933_, lean_object* v_inst_1934_, lean_object* v_fvarId_1935_, lean_object* v_fvarId_x27_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; lean_object* v___x_1940_; 
v___x_1937_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1938_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1939_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1939_, 0, v_fvarId_x27_1936_);
lean_closure_set(v___f_1939_, 1, v___x_1937_);
lean_closure_set(v___f_1939_, 2, v___x_1938_);
lean_closure_set(v___f_1939_, 3, v_fvarId_1935_);
v___x_1940_ = lean_apply_1(v_inst_1934_, v___f_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1941_, lean_object* v_ph_1942_, lean_object* v_inst_1943_, lean_object* v_fvarId_1944_, lean_object* v_fvarId_x27_1945_){
_start:
{
uint8_t v_ph_boxed_1946_; lean_object* v_res_1947_; 
v_ph_boxed_1946_ = lean_unbox(v_ph_1942_);
v_res_1947_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1941_, v_ph_boxed_1946_, v_inst_1943_, v_fvarId_1944_, v_fvarId_x27_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1948_, uint8_t v_t_1949_, lean_object* v_toPure_1950_, lean_object* v_____do__lift_1951_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1951_, v_fvarId_1948_, v_t_1949_);
v___x_1953_ = lean_apply_2(v_toPure_1950_, lean_box(0), v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1954_, lean_object* v_t_1955_, lean_object* v_toPure_1956_, lean_object* v_____do__lift_1957_){
_start:
{
uint8_t v_t_boxed_1958_; lean_object* v_res_1959_; 
v_t_boxed_1958_ = lean_unbox(v_t_1955_);
v_res_1959_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1954_, v_t_boxed_1958_, v_toPure_1956_, v_____do__lift_1957_);
lean_dec_ref(v_____do__lift_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_fvarId_1963_){
_start:
{
lean_object* v_toApplicative_1964_; lean_object* v_toBind_1965_; lean_object* v_toPure_1966_; lean_object* v___x_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; 
v_toApplicative_1964_ = lean_ctor_get(v_inst_1962_, 0);
lean_inc_ref(v_toApplicative_1964_);
v_toBind_1965_ = lean_ctor_get(v_inst_1962_, 1);
lean_inc(v_toBind_1965_);
lean_dec_ref(v_inst_1962_);
v_toPure_1966_ = lean_ctor_get(v_toApplicative_1964_, 1);
lean_inc(v_toPure_1966_);
lean_dec_ref(v_toApplicative_1964_);
v___x_1967_ = lean_box(v_t_1960_);
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1968_, 0, v_fvarId_1963_);
lean_closure_set(v___f_1968_, 1, v___x_1967_);
lean_closure_set(v___f_1968_, 2, v_toPure_1966_);
v___x_1969_ = lean_apply_4(v_toBind_1965_, lean_box(0), lean_box(0), v_inst_1961_, v___f_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_fvarId_1973_){
_start:
{
uint8_t v_t_boxed_1974_; lean_object* v_res_1975_; 
v_t_boxed_1974_ = lean_unbox(v_t_1970_);
v_res_1975_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1974_, v_inst_1971_, v_inst_1972_, v_fvarId_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1976_, uint8_t v_pu_1977_, uint8_t v_t_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_fvarId_1981_){
_start:
{
lean_object* v_toApplicative_1982_; lean_object* v_toBind_1983_; lean_object* v_toPure_1984_; lean_object* v___x_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; 
v_toApplicative_1982_ = lean_ctor_get(v_inst_1980_, 0);
lean_inc_ref(v_toApplicative_1982_);
v_toBind_1983_ = lean_ctor_get(v_inst_1980_, 1);
lean_inc(v_toBind_1983_);
lean_dec_ref(v_inst_1980_);
v_toPure_1984_ = lean_ctor_get(v_toApplicative_1982_, 1);
lean_inc(v_toPure_1984_);
lean_dec_ref(v_toApplicative_1982_);
v___x_1985_ = lean_box(v_t_1978_);
v___f_1986_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1986_, 0, v_fvarId_1981_);
lean_closure_set(v___f_1986_, 1, v___x_1985_);
lean_closure_set(v___f_1986_, 2, v_toPure_1984_);
v___x_1987_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v_inst_1979_, v___f_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1988_, lean_object* v_pu_1989_, lean_object* v_t_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_fvarId_1993_){
_start:
{
uint8_t v_pu_boxed_1994_; uint8_t v_t_boxed_1995_; lean_object* v_res_1996_; 
v_pu_boxed_1994_ = lean_unbox(v_pu_1989_);
v_t_boxed_1995_ = lean_unbox(v_t_1990_);
v_res_1996_ = l_Lean_Compiler_LCNF_normFVar(v_m_1988_, v_pu_boxed_1994_, v_t_boxed_1995_, v_inst_1991_, v_inst_1992_, v_fvarId_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1997_, uint8_t v_t_1998_, lean_object* v_e_1999_, lean_object* v_toPure_2000_, lean_object* v_____do__lift_2001_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1997_, v_____do__lift_2001_, v_t_1998_, v_e_1999_);
v___x_2003_ = lean_apply_2(v_toPure_2000_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2004_, lean_object* v_t_2005_, lean_object* v_e_2006_, lean_object* v_toPure_2007_, lean_object* v_____do__lift_2008_){
_start:
{
uint8_t v_pu_boxed_2009_; uint8_t v_t_boxed_2010_; lean_object* v_res_2011_; 
v_pu_boxed_2009_ = lean_unbox(v_pu_2004_);
v_t_boxed_2010_ = lean_unbox(v_t_2005_);
v_res_2011_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2009_, v_t_boxed_2010_, v_e_2006_, v_toPure_2007_, v_____do__lift_2008_);
lean_dec_ref(v_____do__lift_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2012_, uint8_t v_t_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_e_2016_){
_start:
{
lean_object* v_toApplicative_2017_; lean_object* v_toBind_2018_; lean_object* v_toPure_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___f_2022_; lean_object* v___x_2023_; 
v_toApplicative_2017_ = lean_ctor_get(v_inst_2015_, 0);
lean_inc_ref(v_toApplicative_2017_);
v_toBind_2018_ = lean_ctor_get(v_inst_2015_, 1);
lean_inc(v_toBind_2018_);
lean_dec_ref(v_inst_2015_);
v_toPure_2019_ = lean_ctor_get(v_toApplicative_2017_, 1);
lean_inc(v_toPure_2019_);
lean_dec_ref(v_toApplicative_2017_);
v___x_2020_ = lean_box(v_pu_2012_);
v___x_2021_ = lean_box(v_t_2013_);
v___f_2022_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2022_, 0, v___x_2020_);
lean_closure_set(v___f_2022_, 1, v___x_2021_);
lean_closure_set(v___f_2022_, 2, v_e_2016_);
lean_closure_set(v___f_2022_, 3, v_toPure_2019_);
v___x_2023_ = lean_apply_4(v_toBind_2018_, lean_box(0), lean_box(0), v_inst_2014_, v___f_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2024_, lean_object* v_t_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_e_2028_){
_start:
{
uint8_t v_pu_boxed_2029_; uint8_t v_t_boxed_2030_; lean_object* v_res_2031_; 
v_pu_boxed_2029_ = lean_unbox(v_pu_2024_);
v_t_boxed_2030_ = lean_unbox(v_t_2025_);
v_res_2031_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2029_, v_t_boxed_2030_, v_inst_2026_, v_inst_2027_, v_e_2028_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2032_, uint8_t v_pu_2033_, uint8_t v_t_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_e_2037_){
_start:
{
lean_object* v_toApplicative_2038_; lean_object* v_toBind_2039_; lean_object* v_toPure_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; 
v_toApplicative_2038_ = lean_ctor_get(v_inst_2036_, 0);
lean_inc_ref(v_toApplicative_2038_);
v_toBind_2039_ = lean_ctor_get(v_inst_2036_, 1);
lean_inc(v_toBind_2039_);
lean_dec_ref(v_inst_2036_);
v_toPure_2040_ = lean_ctor_get(v_toApplicative_2038_, 1);
lean_inc(v_toPure_2040_);
lean_dec_ref(v_toApplicative_2038_);
v___x_2041_ = lean_box(v_pu_2033_);
v___x_2042_ = lean_box(v_t_2034_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2043_, 0, v___x_2041_);
lean_closure_set(v___f_2043_, 1, v___x_2042_);
lean_closure_set(v___f_2043_, 2, v_e_2037_);
lean_closure_set(v___f_2043_, 3, v_toPure_2040_);
v___x_2044_ = lean_apply_4(v_toBind_2039_, lean_box(0), lean_box(0), v_inst_2035_, v___f_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2045_, lean_object* v_pu_2046_, lean_object* v_t_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_e_2050_){
_start:
{
uint8_t v_pu_boxed_2051_; uint8_t v_t_boxed_2052_; lean_object* v_res_2053_; 
v_pu_boxed_2051_ = lean_unbox(v_pu_2046_);
v_t_boxed_2052_ = lean_unbox(v_t_2047_);
v_res_2053_ = l_Lean_Compiler_LCNF_normExpr(v_m_2045_, v_pu_boxed_2051_, v_t_boxed_2052_, v_inst_2048_, v_inst_2049_, v_e_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2054_, lean_object* v_arg_2055_, uint8_t v_t_2056_, lean_object* v_toPure_2057_, lean_object* v_____do__lift_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2054_, v_____do__lift_2058_, v_arg_2055_, v_t_2056_);
v___x_2060_ = lean_apply_2(v_toPure_2057_, lean_box(0), v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2061_, lean_object* v_arg_2062_, lean_object* v_t_2063_, lean_object* v_toPure_2064_, lean_object* v_____do__lift_2065_){
_start:
{
uint8_t v_pu_boxed_2066_; uint8_t v_t_boxed_2067_; lean_object* v_res_2068_; 
v_pu_boxed_2066_ = lean_unbox(v_pu_2061_);
v_t_boxed_2067_ = lean_unbox(v_t_2063_);
v_res_2068_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2066_, v_arg_2062_, v_t_boxed_2067_, v_toPure_2064_, v_____do__lift_2065_);
lean_dec_ref(v_____do__lift_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2069_, uint8_t v_t_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_arg_2073_){
_start:
{
lean_object* v_toApplicative_2074_; lean_object* v_toBind_2075_; lean_object* v_toPure_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___f_2079_; lean_object* v___x_2080_; 
v_toApplicative_2074_ = lean_ctor_get(v_inst_2072_, 0);
lean_inc_ref(v_toApplicative_2074_);
v_toBind_2075_ = lean_ctor_get(v_inst_2072_, 1);
lean_inc(v_toBind_2075_);
lean_dec_ref(v_inst_2072_);
v_toPure_2076_ = lean_ctor_get(v_toApplicative_2074_, 1);
lean_inc(v_toPure_2076_);
lean_dec_ref(v_toApplicative_2074_);
v___x_2077_ = lean_box(v_pu_2069_);
v___x_2078_ = lean_box(v_t_2070_);
v___f_2079_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2079_, 0, v___x_2077_);
lean_closure_set(v___f_2079_, 1, v_arg_2073_);
lean_closure_set(v___f_2079_, 2, v___x_2078_);
lean_closure_set(v___f_2079_, 3, v_toPure_2076_);
v___x_2080_ = lean_apply_4(v_toBind_2075_, lean_box(0), lean_box(0), v_inst_2071_, v___f_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2081_, lean_object* v_t_2082_, lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_arg_2085_){
_start:
{
uint8_t v_pu_boxed_2086_; uint8_t v_t_boxed_2087_; lean_object* v_res_2088_; 
v_pu_boxed_2086_ = lean_unbox(v_pu_2081_);
v_t_boxed_2087_ = lean_unbox(v_t_2082_);
v_res_2088_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2086_, v_t_boxed_2087_, v_inst_2083_, v_inst_2084_, v_arg_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2089_, uint8_t v_pu_2090_, uint8_t v_t_2091_, lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_arg_2094_){
_start:
{
lean_object* v_toApplicative_2095_; lean_object* v_toBind_2096_; lean_object* v_toPure_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; 
v_toApplicative_2095_ = lean_ctor_get(v_inst_2093_, 0);
lean_inc_ref(v_toApplicative_2095_);
v_toBind_2096_ = lean_ctor_get(v_inst_2093_, 1);
lean_inc(v_toBind_2096_);
lean_dec_ref(v_inst_2093_);
v_toPure_2097_ = lean_ctor_get(v_toApplicative_2095_, 1);
lean_inc(v_toPure_2097_);
lean_dec_ref(v_toApplicative_2095_);
v___x_2098_ = lean_box(v_pu_2090_);
v___x_2099_ = lean_box(v_t_2091_);
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2100_, 0, v___x_2098_);
lean_closure_set(v___f_2100_, 1, v_arg_2094_);
lean_closure_set(v___f_2100_, 2, v___x_2099_);
lean_closure_set(v___f_2100_, 3, v_toPure_2097_);
v___x_2101_ = lean_apply_4(v_toBind_2096_, lean_box(0), lean_box(0), v_inst_2092_, v___f_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2102_, lean_object* v_pu_2103_, lean_object* v_t_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_arg_2107_){
_start:
{
uint8_t v_pu_boxed_2108_; uint8_t v_t_boxed_2109_; lean_object* v_res_2110_; 
v_pu_boxed_2108_ = lean_unbox(v_pu_2103_);
v_t_boxed_2109_ = lean_unbox(v_t_2104_);
v_res_2110_ = l_Lean_Compiler_LCNF_normArg(v_m_2102_, v_pu_boxed_2108_, v_t_boxed_2109_, v_inst_2105_, v_inst_2106_, v_arg_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2111_, lean_object* v_e_2112_, uint8_t v_t_2113_, lean_object* v_toPure_2114_, lean_object* v_____do__lift_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2111_, v_____do__lift_2115_, v_e_2112_, v_t_2113_);
v___x_2117_ = lean_apply_2(v_toPure_2114_, lean_box(0), v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2118_, lean_object* v_e_2119_, lean_object* v_t_2120_, lean_object* v_toPure_2121_, lean_object* v_____do__lift_2122_){
_start:
{
uint8_t v_pu_boxed_2123_; uint8_t v_t_boxed_2124_; lean_object* v_res_2125_; 
v_pu_boxed_2123_ = lean_unbox(v_pu_2118_);
v_t_boxed_2124_ = lean_unbox(v_t_2120_);
v_res_2125_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2123_, v_e_2119_, v_t_boxed_2124_, v_toPure_2121_, v_____do__lift_2122_);
lean_dec_ref(v_____do__lift_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2126_, uint8_t v_t_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_e_2130_){
_start:
{
lean_object* v_toApplicative_2131_; lean_object* v_toBind_2132_; lean_object* v_toPure_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; 
v_toApplicative_2131_ = lean_ctor_get(v_inst_2129_, 0);
lean_inc_ref(v_toApplicative_2131_);
v_toBind_2132_ = lean_ctor_get(v_inst_2129_, 1);
lean_inc(v_toBind_2132_);
lean_dec_ref(v_inst_2129_);
v_toPure_2133_ = lean_ctor_get(v_toApplicative_2131_, 1);
lean_inc(v_toPure_2133_);
lean_dec_ref(v_toApplicative_2131_);
v___x_2134_ = lean_box(v_pu_2126_);
v___x_2135_ = lean_box(v_t_2127_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2136_, 0, v___x_2134_);
lean_closure_set(v___f_2136_, 1, v_e_2130_);
lean_closure_set(v___f_2136_, 2, v___x_2135_);
lean_closure_set(v___f_2136_, 3, v_toPure_2133_);
v___x_2137_ = lean_apply_4(v_toBind_2132_, lean_box(0), lean_box(0), v_inst_2128_, v___f_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2138_, lean_object* v_t_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_e_2142_){
_start:
{
uint8_t v_pu_boxed_2143_; uint8_t v_t_boxed_2144_; lean_object* v_res_2145_; 
v_pu_boxed_2143_ = lean_unbox(v_pu_2138_);
v_t_boxed_2144_ = lean_unbox(v_t_2139_);
v_res_2145_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2143_, v_t_boxed_2144_, v_inst_2140_, v_inst_2141_, v_e_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2146_, uint8_t v_pu_2147_, uint8_t v_t_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_e_2151_){
_start:
{
lean_object* v_toApplicative_2152_; lean_object* v_toBind_2153_; lean_object* v_toPure_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___f_2157_; lean_object* v___x_2158_; 
v_toApplicative_2152_ = lean_ctor_get(v_inst_2150_, 0);
lean_inc_ref(v_toApplicative_2152_);
v_toBind_2153_ = lean_ctor_get(v_inst_2150_, 1);
lean_inc(v_toBind_2153_);
lean_dec_ref(v_inst_2150_);
v_toPure_2154_ = lean_ctor_get(v_toApplicative_2152_, 1);
lean_inc(v_toPure_2154_);
lean_dec_ref(v_toApplicative_2152_);
v___x_2155_ = lean_box(v_pu_2147_);
v___x_2156_ = lean_box(v_t_2148_);
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2157_, 0, v___x_2155_);
lean_closure_set(v___f_2157_, 1, v_e_2151_);
lean_closure_set(v___f_2157_, 2, v___x_2156_);
lean_closure_set(v___f_2157_, 3, v_toPure_2154_);
v___x_2158_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v_inst_2149_, v___f_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2159_, lean_object* v_pu_2160_, lean_object* v_t_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_e_2164_){
_start:
{
uint8_t v_pu_boxed_2165_; uint8_t v_t_boxed_2166_; lean_object* v_res_2167_; 
v_pu_boxed_2165_ = lean_unbox(v_pu_2160_);
v_t_boxed_2166_ = lean_unbox(v_t_2161_);
v_res_2167_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2159_, v_pu_boxed_2165_, v_t_boxed_2166_, v_inst_2162_, v_inst_2163_, v_e_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2168_, lean_object* v_s_2169_, lean_object* v_e_2170_, uint8_t v_translator_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2168_, v_s_2169_, v_translator_2171_, v_e_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2173_, lean_object* v_s_2174_, lean_object* v_e_2175_, lean_object* v_translator_2176_){
_start:
{
uint8_t v_pu_boxed_2177_; uint8_t v_translator_boxed_2178_; lean_object* v_res_2179_; 
v_pu_boxed_2177_ = lean_unbox(v_pu_2173_);
v_translator_boxed_2178_ = lean_unbox(v_translator_2176_);
v_res_2179_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2177_, v_s_2174_, v_e_2175_, v_translator_boxed_2178_);
lean_dec_ref(v_s_2174_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2180_, lean_object* v_args_2181_, uint8_t v_t_2182_, lean_object* v_toPure_2183_, lean_object* v_____do__lift_2184_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2180_, v_____do__lift_2184_, v_args_2181_, v_t_2182_);
v___x_2186_ = lean_apply_2(v_toPure_2183_, lean_box(0), v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2187_, lean_object* v_args_2188_, lean_object* v_t_2189_, lean_object* v_toPure_2190_, lean_object* v_____do__lift_2191_){
_start:
{
uint8_t v_pu_boxed_2192_; uint8_t v_t_boxed_2193_; lean_object* v_res_2194_; 
v_pu_boxed_2192_ = lean_unbox(v_pu_2187_);
v_t_boxed_2193_ = lean_unbox(v_t_2189_);
v_res_2194_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2192_, v_args_2188_, v_t_boxed_2193_, v_toPure_2190_, v_____do__lift_2191_);
lean_dec_ref(v_____do__lift_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2195_, uint8_t v_t_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_args_2199_){
_start:
{
lean_object* v_toApplicative_2200_; lean_object* v_toBind_2201_; lean_object* v_toPure_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; 
v_toApplicative_2200_ = lean_ctor_get(v_inst_2198_, 0);
lean_inc_ref(v_toApplicative_2200_);
v_toBind_2201_ = lean_ctor_get(v_inst_2198_, 1);
lean_inc(v_toBind_2201_);
lean_dec_ref(v_inst_2198_);
v_toPure_2202_ = lean_ctor_get(v_toApplicative_2200_, 1);
lean_inc(v_toPure_2202_);
lean_dec_ref(v_toApplicative_2200_);
v___x_2203_ = lean_box(v_pu_2195_);
v___x_2204_ = lean_box(v_t_2196_);
v___f_2205_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2205_, 0, v___x_2203_);
lean_closure_set(v___f_2205_, 1, v_args_2199_);
lean_closure_set(v___f_2205_, 2, v___x_2204_);
lean_closure_set(v___f_2205_, 3, v_toPure_2202_);
v___x_2206_ = lean_apply_4(v_toBind_2201_, lean_box(0), lean_box(0), v_inst_2197_, v___f_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2207_, lean_object* v_t_2208_, lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_args_2211_){
_start:
{
uint8_t v_pu_boxed_2212_; uint8_t v_t_boxed_2213_; lean_object* v_res_2214_; 
v_pu_boxed_2212_ = lean_unbox(v_pu_2207_);
v_t_boxed_2213_ = lean_unbox(v_t_2208_);
v_res_2214_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2212_, v_t_boxed_2213_, v_inst_2209_, v_inst_2210_, v_args_2211_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2215_, uint8_t v_pu_2216_, uint8_t v_t_2217_, lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_args_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2216_, v_t_2217_, v_inst_2218_, v_inst_2219_, v_args_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2222_, lean_object* v_pu_2223_, lean_object* v_t_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_args_2227_){
_start:
{
uint8_t v_pu_boxed_2228_; uint8_t v_t_boxed_2229_; lean_object* v_res_2230_; 
v_pu_boxed_2228_ = lean_unbox(v_pu_2223_);
v_t_boxed_2229_ = lean_unbox(v_t_2224_);
v_res_2230_ = l_Lean_Compiler_LCNF_normArgs(v_m_2222_, v_pu_boxed_2228_, v_t_boxed_2229_, v_inst_2225_, v_inst_2226_, v_args_2227_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v_nextIdx_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_lctx_2238_; lean_object* v_nextIdx_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2250_; 
v___x_2234_ = lean_st_ref_get(v_a_2232_);
v_nextIdx_2235_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_nextIdx_2235_);
lean_dec(v___x_2234_);
v___x_2236_ = l_Lean_Name_num___override(v_binderName_2231_, v_nextIdx_2235_);
v___x_2237_ = lean_st_ref_take(v_a_2232_);
v_lctx_2238_ = lean_ctor_get(v___x_2237_, 0);
v_nextIdx_2239_ = lean_ctor_get(v___x_2237_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2250_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_nextIdx_2239_);
lean_inc(v_lctx_2238_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2250_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2243_ = lean_unsigned_to_nat(1u);
v___x_2244_ = lean_nat_add(v_nextIdx_2239_, v___x_2243_);
lean_dec(v_nextIdx_2239_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_lctx_2238_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_st_ref_put(v_a_2232_, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2236_);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2251_, v_a_2252_);
lean_dec(v_a_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2255_, v_a_2257_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2269_, lean_object* v_baseName_2270_, lean_object* v_a_2271_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = l_Lean_Name_isAnonymous(v_binderName_2269_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_dec(v_baseName_2270_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_binderName_2269_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; 
lean_dec(v_binderName_2269_);
v___x_2275_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2270_, v_a_2271_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2276_, lean_object* v_baseName_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2276_, v_baseName_2277_, v_a_2278_);
lean_dec(v_a_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2281_, lean_object* v_baseName_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2281_, v_baseName_2282_, v_a_2284_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2289_, lean_object* v_baseName_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2289_, v_baseName_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; lean_object* v_ngen_2300_; lean_object* v_namePrefix_2301_; lean_object* v_idx_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2331_; 
v___x_2299_ = lean_st_ref_get(v___y_2297_);
v_ngen_2300_ = lean_ctor_get(v___x_2299_, 2);
lean_inc_ref(v_ngen_2300_);
lean_dec(v___x_2299_);
v_namePrefix_2301_ = lean_ctor_get(v_ngen_2300_, 0);
v_idx_2302_ = lean_ctor_get(v_ngen_2300_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_ngen_2300_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2304_ = v_ngen_2300_;
v_isShared_2305_ = v_isSharedCheck_2331_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_idx_2302_);
lean_inc(v_namePrefix_2301_);
lean_dec(v_ngen_2300_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2331_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_r_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
lean_inc(v_idx_2302_);
lean_inc(v_namePrefix_2301_);
v_r_2306_ = l_Lean_Name_num___override(v_namePrefix_2301_, v_idx_2302_);
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_nat_add(v_idx_2302_, v___x_2307_);
lean_dec(v_idx_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2308_);
v___x_2310_ = v___x_2304_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_namePrefix_2301_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v_env_2312_; lean_object* v_nextMacroScope_2313_; lean_object* v_auxDeclNGen_2314_; lean_object* v_traceState_2315_; lean_object* v_cache_2316_; lean_object* v_messages_2317_; lean_object* v_infoState_2318_; lean_object* v_snapshotTasks_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2328_; 
v___x_2311_ = lean_st_ref_take(v___y_2297_);
v_env_2312_ = lean_ctor_get(v___x_2311_, 0);
v_nextMacroScope_2313_ = lean_ctor_get(v___x_2311_, 1);
v_auxDeclNGen_2314_ = lean_ctor_get(v___x_2311_, 3);
v_traceState_2315_ = lean_ctor_get(v___x_2311_, 4);
v_cache_2316_ = lean_ctor_get(v___x_2311_, 5);
v_messages_2317_ = lean_ctor_get(v___x_2311_, 6);
v_infoState_2318_ = lean_ctor_get(v___x_2311_, 7);
v_snapshotTasks_2319_ = lean_ctor_get(v___x_2311_, 8);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v___x_2311_, 2);
lean_dec(v_unused_2329_);
v___x_2321_ = v___x_2311_;
v_isShared_2322_ = v_isSharedCheck_2328_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_snapshotTasks_2319_);
lean_inc(v_infoState_2318_);
lean_inc(v_messages_2317_);
lean_inc(v_cache_2316_);
lean_inc(v_traceState_2315_);
lean_inc(v_auxDeclNGen_2314_);
lean_inc(v_nextMacroScope_2313_);
lean_inc(v_env_2312_);
lean_dec(v___x_2311_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2328_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 2, v___x_2310_);
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_env_2312_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_nextMacroScope_2313_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_auxDeclNGen_2314_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_traceState_2315_);
lean_ctor_set(v_reuseFailAlloc_2327_, 5, v_cache_2316_);
lean_ctor_set(v_reuseFailAlloc_2327_, 6, v_messages_2317_);
lean_ctor_set(v_reuseFailAlloc_2327_, 7, v_infoState_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 8, v_snapshotTasks_2319_);
v___x_2324_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_st_ref_put(v___y_2297_, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_r_2306_);
return v___x_2326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2332_);
lean_dec(v___y_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v___x_2340_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2338_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2358_, lean_object* v_binderName_2359_, lean_object* v_type_2360_, uint8_t v_borrow_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2391_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2369_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2370_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2359_, v___x_2369_, v_a_2363_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2391_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2391_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_lctx_2377_; lean_object* v_nextIdx_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2390_; 
v___x_2375_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2375_, 0, v_a_2368_);
lean_ctor_set(v___x_2375_, 1, v_a_2371_);
lean_ctor_set(v___x_2375_, 2, v_type_2360_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*3, v_borrow_2361_);
v___x_2376_ = lean_st_ref_take(v_a_2363_);
v_lctx_2377_ = lean_ctor_get(v___x_2376_, 0);
v_nextIdx_2378_ = lean_ctor_get(v___x_2376_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2380_ = v___x_2376_;
v_isShared_2381_ = v_isSharedCheck_2390_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_nextIdx_2378_);
lean_inc(v_lctx_2377_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2390_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_inc_ref(v___x_2375_);
v___x_2382_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2358_, v_lctx_2377_, v___x_2375_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2382_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_nextIdx_2378_);
v___x_2384_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = lean_st_ref_put(v_a_2363_, v___x_2384_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2375_);
v___x_2387_ = v___x_2373_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2375_);
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
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec_ref(v_type_2360_);
lean_dec(v_binderName_2359_);
v_a_2392_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2367_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2367_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2400_, lean_object* v_binderName_2401_, lean_object* v_type_2402_, lean_object* v_borrow_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
uint8_t v_pu_boxed_2409_; uint8_t v_borrow_boxed_2410_; lean_object* v_res_2411_; 
v_pu_boxed_2409_ = lean_unbox(v_pu_2400_);
v_borrow_boxed_2410_ = lean_unbox(v_borrow_2403_);
v_res_2411_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2409_, v_binderName_2401_, v_type_2402_, v_borrow_boxed_2410_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2427_, lean_object* v_binderName_2428_, lean_object* v_type_2429_, lean_object* v_value_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2460_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2439_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2428_, v___x_2438_, v_a_2432_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2460_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2460_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_lctx_2446_; lean_object* v_nextIdx_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2459_; 
v___x_2444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2444_, 0, v_a_2437_);
lean_ctor_set(v___x_2444_, 1, v_a_2440_);
lean_ctor_set(v___x_2444_, 2, v_type_2429_);
lean_ctor_set(v___x_2444_, 3, v_value_2430_);
v___x_2445_ = lean_st_ref_take(v_a_2432_);
v_lctx_2446_ = lean_ctor_get(v___x_2445_, 0);
v_nextIdx_2447_ = lean_ctor_get(v___x_2445_, 1);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2449_ = v___x_2445_;
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_nextIdx_2447_);
lean_inc(v_lctx_2446_);
lean_dec(v___x_2445_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_inc_ref(v___x_2444_);
v___x_2451_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2427_, v_lctx_2446_, v___x_2444_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2453_ = v___x_2449_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_nextIdx_2447_);
v___x_2453_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_st_ref_put(v_a_2432_, v___x_2453_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2444_);
v___x_2456_ = v___x_2442_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2444_);
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
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_value_2430_);
lean_dec_ref(v_type_2429_);
lean_dec(v_binderName_2428_);
v_a_2461_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2436_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2436_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2469_, lean_object* v_binderName_2470_, lean_object* v_type_2471_, lean_object* v_value_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
uint8_t v_pu_boxed_2478_; lean_object* v_res_2479_; 
v_pu_boxed_2478_ = lean_unbox(v_pu_2469_);
v_res_2479_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2478_, v_binderName_2470_, v_type_2471_, v_value_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2483_, lean_object* v_binderName_2484_, lean_object* v_type_2485_, lean_object* v_params_2486_, lean_object* v_value_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2517_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2495_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2496_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2484_, v___x_2495_, v_a_2489_);
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2517_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2517_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_lctx_2503_; lean_object* v_nextIdx_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2516_; 
v___x_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2494_);
lean_ctor_set(v___x_2501_, 1, v_a_2497_);
lean_ctor_set(v___x_2501_, 2, v_params_2486_);
lean_ctor_set(v___x_2501_, 3, v_type_2485_);
lean_ctor_set(v___x_2501_, 4, v_value_2487_);
v___x_2502_ = lean_st_ref_take(v_a_2489_);
v_lctx_2503_ = lean_ctor_get(v___x_2502_, 0);
v_nextIdx_2504_ = lean_ctor_get(v___x_2502_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2506_ = v___x_2502_;
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_nextIdx_2504_);
lean_inc(v_lctx_2503_);
lean_dec(v___x_2502_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_inc_ref(v___x_2501_);
v___x_2508_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2483_, v_lctx_2503_, v___x_2501_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_nextIdx_2504_);
v___x_2510_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2511_ = lean_st_ref_put(v_a_2489_, v___x_2510_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2501_);
v___x_2513_ = v___x_2499_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2501_);
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
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_value_2487_);
lean_dec_ref(v_params_2486_);
lean_dec_ref(v_type_2485_);
lean_dec(v_binderName_2484_);
v_a_2518_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2493_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2493_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2526_, lean_object* v_binderName_2527_, lean_object* v_type_2528_, lean_object* v_params_2529_, lean_object* v_value_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
uint8_t v_pu_boxed_2536_; lean_object* v_res_2537_; 
v_pu_boxed_2536_ = lean_unbox(v_pu_2526_);
v_res_2537_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2536_, v_binderName_2527_, v_type_2528_, v_params_2529_, v_value_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2544_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2545_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2544_, v_a_2540_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2548_ = lean_box(1);
v___x_2549_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2538_, v_a_2546_, v___x_2547_, v___x_2548_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
uint8_t v_pu_boxed_2556_; lean_object* v_res_2557_; 
v_pu_boxed_2556_ = lean_unbox(v_pu_2550_);
v_res_2557_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2556_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2575_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_fvarId_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v_fvarId_2569_ = lean_ctor_get(v_a_2565_, 0);
lean_inc(v_fvarId_2569_);
v___x_2570_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_fvarId_2569_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2565_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2571_);
v___x_2573_ = v___x_2567_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2564_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2564_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
uint8_t v_pu_boxed_2590_; lean_object* v_res_2591_; 
v_pu_boxed_2590_ = lean_unbox(v_pu_2584_);
v_res_2591_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2590_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2592_, lean_object* v_p_2593_, lean_object* v_type_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_fvarId_2597_; lean_object* v_binderName_2598_; lean_object* v_type_2599_; uint8_t v_borrow_2600_; size_t v___x_2601_; size_t v___x_2602_; uint8_t v___x_2603_; 
v_fvarId_2597_ = lean_ctor_get(v_p_2593_, 0);
v_binderName_2598_ = lean_ctor_get(v_p_2593_, 1);
v_type_2599_ = lean_ctor_get(v_p_2593_, 2);
v_borrow_2600_ = lean_ctor_get_uint8(v_p_2593_, sizeof(void*)*3);
v___x_2601_ = lean_ptr_addr(v_type_2594_);
v___x_2602_ = lean_ptr_addr(v_type_2599_);
v___x_2603_ = lean_usize_dec_eq(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2623_; 
lean_inc(v_binderName_2598_);
lean_inc(v_fvarId_2597_);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_p_2593_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; lean_object* v_unused_2625_; lean_object* v_unused_2626_; 
v_unused_2624_ = lean_ctor_get(v_p_2593_, 2);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_p_2593_, 1);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_p_2593_, 0);
lean_dec(v_unused_2626_);
v___x_2605_ = v_p_2593_;
v_isShared_2606_ = v_isSharedCheck_2623_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v_p_2593_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2623_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_p_2608_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 2, v_type_2594_);
v_p_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_fvarId_2597_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_binderName_2598_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_type_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, sizeof(void*)*3, v_borrow_2600_);
v_p_2608_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; lean_object* v_lctx_2610_; lean_object* v_nextIdx_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2621_; 
v___x_2609_ = lean_st_ref_take(v_a_2595_);
v_lctx_2610_ = lean_ctor_get(v___x_2609_, 0);
v_nextIdx_2611_ = lean_ctor_get(v___x_2609_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2613_ = v___x_2609_;
v_isShared_2614_ = v_isSharedCheck_2621_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_nextIdx_2611_);
lean_inc(v_lctx_2610_);
lean_dec(v___x_2609_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2621_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_inc_ref(v_p_2608_);
v___x_2615_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2592_, v_lctx_2610_, v_p_2608_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2615_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_nextIdx_2611_);
v___x_2617_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_st_ref_put(v_a_2595_, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_p_2608_);
return v___x_2619_;
}
}
}
}
}
else
{
lean_object* v___x_2627_; 
lean_dec_ref(v_type_2594_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_p_2593_);
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2628_, lean_object* v_p_2629_, lean_object* v_type_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
uint8_t v_pu_boxed_2633_; lean_object* v_res_2634_; 
v_pu_boxed_2633_ = lean_unbox(v_pu_2628_);
v_res_2634_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2633_, v_p_2629_, v_type_2630_, v_a_2631_);
lean_dec(v_a_2631_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2635_, lean_object* v_p_2636_, lean_object* v_type_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2635_, v_p_2636_, v_type_2637_, v_a_2639_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2644_, lean_object* v_p_2645_, lean_object* v_type_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
uint8_t v_pu_boxed_2652_; lean_object* v_res_2653_; 
v_pu_boxed_2652_ = lean_unbox(v_pu_2644_);
v_res_2653_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2652_, v_p_2645_, v_type_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2654_, lean_object* v_p_2655_, uint8_t v_borrow_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_fvarId_2659_; lean_object* v_binderName_2660_; lean_object* v_type_2661_; uint8_t v_borrow_2662_; 
v_fvarId_2659_ = lean_ctor_get(v_p_2655_, 0);
v_binderName_2660_ = lean_ctor_get(v_p_2655_, 1);
v_type_2661_ = lean_ctor_get(v_p_2655_, 2);
v_borrow_2662_ = lean_ctor_get_uint8(v_p_2655_, sizeof(void*)*3);
if (v_borrow_2662_ == 0)
{
if (v_borrow_2656_ == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_p_2655_);
return v___x_2678_;
}
else
{
lean_inc_ref(v_type_2661_);
lean_inc(v_binderName_2660_);
lean_inc(v_fvarId_2659_);
lean_dec_ref(v_p_2655_);
goto v___jp_2663_;
}
}
else
{
if (v_borrow_2656_ == 0)
{
lean_inc_ref(v_type_2661_);
lean_inc(v_binderName_2660_);
lean_inc(v_fvarId_2659_);
lean_dec_ref(v_p_2655_);
goto v___jp_2663_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_p_2655_);
return v___x_2679_;
}
}
v___jp_2663_:
{
lean_object* v_p_2664_; lean_object* v___x_2665_; lean_object* v_lctx_2666_; lean_object* v_nextIdx_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2677_; 
v_p_2664_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2664_, 0, v_fvarId_2659_);
lean_ctor_set(v_p_2664_, 1, v_binderName_2660_);
lean_ctor_set(v_p_2664_, 2, v_type_2661_);
lean_ctor_set_uint8(v_p_2664_, sizeof(void*)*3, v_borrow_2656_);
v___x_2665_ = lean_st_ref_take(v_a_2657_);
v_lctx_2666_ = lean_ctor_get(v___x_2665_, 0);
v_nextIdx_2667_ = lean_ctor_get(v___x_2665_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2669_ = v___x_2665_;
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_nextIdx_2667_);
lean_inc(v_lctx_2666_);
lean_dec(v___x_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_inc_ref(v_p_2664_);
v___x_2671_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2654_, v_lctx_2666_, v_p_2664_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_nextIdx_2667_);
v___x_2673_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_st_ref_put(v_a_2657_, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_p_2664_);
return v___x_2675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2680_, lean_object* v_p_2681_, lean_object* v_borrow_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
uint8_t v_pu_boxed_2685_; uint8_t v_borrow_boxed_2686_; lean_object* v_res_2687_; 
v_pu_boxed_2685_ = lean_unbox(v_pu_2680_);
v_borrow_boxed_2686_ = lean_unbox(v_borrow_2682_);
v_res_2687_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2685_, v_p_2681_, v_borrow_boxed_2686_, v_a_2683_);
lean_dec(v_a_2683_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2688_, lean_object* v_p_2689_, uint8_t v_borrow_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2688_, v_p_2689_, v_borrow_2690_, v_a_2692_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2697_, lean_object* v_p_2698_, lean_object* v_borrow_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
uint8_t v_pu_boxed_2705_; uint8_t v_borrow_boxed_2706_; lean_object* v_res_2707_; 
v_pu_boxed_2705_ = lean_unbox(v_pu_2697_);
v_borrow_boxed_2706_ = lean_unbox(v_borrow_2699_);
v_res_2707_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2705_, v_p_2698_, v_borrow_boxed_2706_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2708_, lean_object* v_decl_2709_, lean_object* v_type_2710_, lean_object* v_value_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_fvarId_2714_; lean_object* v_binderName_2715_; lean_object* v_type_2716_; lean_object* v_value_2717_; size_t v___x_2733_; size_t v___x_2734_; uint8_t v___x_2735_; 
v_fvarId_2714_ = lean_ctor_get(v_decl_2709_, 0);
v_binderName_2715_ = lean_ctor_get(v_decl_2709_, 1);
v_type_2716_ = lean_ctor_get(v_decl_2709_, 2);
v_value_2717_ = lean_ctor_get(v_decl_2709_, 3);
v___x_2733_ = lean_ptr_addr(v_type_2710_);
v___x_2734_ = lean_ptr_addr(v_type_2716_);
v___x_2735_ = lean_usize_dec_eq(v___x_2733_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_inc(v_binderName_2715_);
lean_inc(v_fvarId_2714_);
lean_dec_ref(v_decl_2709_);
goto v___jp_2718_;
}
else
{
size_t v___x_2736_; size_t v___x_2737_; uint8_t v___x_2738_; 
v___x_2736_ = lean_ptr_addr(v_value_2711_);
v___x_2737_ = lean_ptr_addr(v_value_2717_);
v___x_2738_ = lean_usize_dec_eq(v___x_2736_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_inc(v_binderName_2715_);
lean_inc(v_fvarId_2714_);
lean_dec_ref(v_decl_2709_);
goto v___jp_2718_;
}
else
{
lean_object* v___x_2739_; 
lean_dec(v_value_2711_);
lean_dec_ref(v_type_2710_);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_decl_2709_);
return v___x_2739_;
}
}
v___jp_2718_:
{
lean_object* v_decl_2719_; lean_object* v___x_2720_; lean_object* v_lctx_2721_; lean_object* v_nextIdx_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2732_; 
v_decl_2719_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2719_, 0, v_fvarId_2714_);
lean_ctor_set(v_decl_2719_, 1, v_binderName_2715_);
lean_ctor_set(v_decl_2719_, 2, v_type_2710_);
lean_ctor_set(v_decl_2719_, 3, v_value_2711_);
v___x_2720_ = lean_st_ref_take(v_a_2712_);
v_lctx_2721_ = lean_ctor_get(v___x_2720_, 0);
v_nextIdx_2722_ = lean_ctor_get(v___x_2720_, 1);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2724_ = v___x_2720_;
v_isShared_2725_ = v_isSharedCheck_2732_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_nextIdx_2722_);
lean_inc(v_lctx_2721_);
lean_dec(v___x_2720_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2732_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_inc_ref(v_decl_2719_);
v___x_2726_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2708_, v_lctx_2721_, v_decl_2719_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_nextIdx_2722_);
v___x_2728_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = lean_st_ref_put(v_a_2712_, v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_decl_2719_);
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2740_, lean_object* v_decl_2741_, lean_object* v_type_2742_, lean_object* v_value_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
uint8_t v_pu_boxed_2746_; lean_object* v_res_2747_; 
v_pu_boxed_2746_ = lean_unbox(v_pu_2740_);
v_res_2747_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2746_, v_decl_2741_, v_type_2742_, v_value_2743_, v_a_2744_);
lean_dec(v_a_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2748_, lean_object* v_decl_2749_, lean_object* v_type_2750_, lean_object* v_value_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2748_, v_decl_2749_, v_type_2750_, v_value_2751_, v_a_2753_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2758_, lean_object* v_decl_2759_, lean_object* v_type_2760_, lean_object* v_value_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
uint8_t v_pu_boxed_2767_; lean_object* v_res_2768_; 
v_pu_boxed_2767_ = lean_unbox(v_pu_2758_);
v_res_2768_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2767_, v_decl_2759_, v_type_2760_, v_value_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2769_, lean_object* v_decl_2770_, lean_object* v_value_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_type_2774_; lean_object* v___x_2775_; 
v_type_2774_ = lean_ctor_get(v_decl_2770_, 2);
lean_inc_ref(v_type_2774_);
v___x_2775_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2769_, v_decl_2770_, v_type_2774_, v_value_2771_, v_a_2772_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2776_, lean_object* v_decl_2777_, lean_object* v_value_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
uint8_t v_pu_boxed_2781_; lean_object* v_res_2782_; 
v_pu_boxed_2781_ = lean_unbox(v_pu_2776_);
v_res_2782_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2781_, v_decl_2777_, v_value_2778_, v_a_2779_);
lean_dec(v_a_2779_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2783_, lean_object* v_decl_2784_, lean_object* v_value_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2783_, v_decl_2784_, v_value_2785_, v_a_2787_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2792_, lean_object* v_decl_2793_, lean_object* v_value_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
uint8_t v_pu_boxed_2800_; lean_object* v_res_2801_; 
v_pu_boxed_2800_ = lean_unbox(v_pu_2792_);
v_res_2801_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2800_, v_decl_2793_, v_value_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2802_, lean_object* v_decl_2803_, lean_object* v_type_2804_, lean_object* v_params_2805_, lean_object* v_value_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_fvarId_2809_; lean_object* v_binderName_2810_; lean_object* v_params_2811_; lean_object* v_type_2812_; lean_object* v_value_2813_; size_t v___x_2829_; size_t v___x_2830_; uint8_t v___x_2831_; 
v_fvarId_2809_ = lean_ctor_get(v_decl_2803_, 0);
v_binderName_2810_ = lean_ctor_get(v_decl_2803_, 1);
v_params_2811_ = lean_ctor_get(v_decl_2803_, 2);
v_type_2812_ = lean_ctor_get(v_decl_2803_, 3);
v_value_2813_ = lean_ctor_get(v_decl_2803_, 4);
v___x_2829_ = lean_ptr_addr(v_type_2804_);
v___x_2830_ = lean_ptr_addr(v_type_2812_);
v___x_2831_ = lean_usize_dec_eq(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_inc(v_binderName_2810_);
lean_inc(v_fvarId_2809_);
lean_dec_ref(v_decl_2803_);
goto v___jp_2814_;
}
else
{
size_t v___x_2832_; size_t v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = lean_ptr_addr(v_params_2805_);
v___x_2833_ = lean_ptr_addr(v_params_2811_);
v___x_2834_ = lean_usize_dec_eq(v___x_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_inc(v_binderName_2810_);
lean_inc(v_fvarId_2809_);
lean_dec_ref(v_decl_2803_);
goto v___jp_2814_;
}
else
{
size_t v___x_2835_; size_t v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = lean_ptr_addr(v_value_2806_);
v___x_2836_ = lean_ptr_addr(v_value_2813_);
v___x_2837_ = lean_usize_dec_eq(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_inc(v_binderName_2810_);
lean_inc(v_fvarId_2809_);
lean_dec_ref(v_decl_2803_);
goto v___jp_2814_;
}
else
{
lean_object* v___x_2838_; 
lean_dec_ref(v_value_2806_);
lean_dec_ref(v_params_2805_);
lean_dec_ref(v_type_2804_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_decl_2803_);
return v___x_2838_;
}
}
}
v___jp_2814_:
{
lean_object* v_decl_2815_; lean_object* v___x_2816_; lean_object* v_lctx_2817_; lean_object* v_nextIdx_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2828_; 
v_decl_2815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2815_, 0, v_fvarId_2809_);
lean_ctor_set(v_decl_2815_, 1, v_binderName_2810_);
lean_ctor_set(v_decl_2815_, 2, v_params_2805_);
lean_ctor_set(v_decl_2815_, 3, v_type_2804_);
lean_ctor_set(v_decl_2815_, 4, v_value_2806_);
v___x_2816_ = lean_st_ref_take(v_a_2807_);
v_lctx_2817_ = lean_ctor_get(v___x_2816_, 0);
v_nextIdx_2818_ = lean_ctor_get(v___x_2816_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2820_ = v___x_2816_;
v_isShared_2821_ = v_isSharedCheck_2828_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_nextIdx_2818_);
lean_inc(v_lctx_2817_);
lean_dec(v___x_2816_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2828_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
lean_inc_ref(v_decl_2815_);
v___x_2822_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2802_, v_lctx_2817_, v_decl_2815_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_nextIdx_2818_);
v___x_2824_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_st_ref_put(v_a_2807_, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_decl_2815_);
return v___x_2826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2839_, lean_object* v_decl_2840_, lean_object* v_type_2841_, lean_object* v_params_2842_, lean_object* v_value_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
uint8_t v_pu_boxed_2846_; lean_object* v_res_2847_; 
v_pu_boxed_2846_ = lean_unbox(v_pu_2839_);
v_res_2847_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2846_, v_decl_2840_, v_type_2841_, v_params_2842_, v_value_2843_, v_a_2844_);
lean_dec(v_a_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2848_, lean_object* v_decl_2849_, lean_object* v_type_2850_, lean_object* v_params_2851_, lean_object* v_value_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2848_, v_decl_2849_, v_type_2850_, v_params_2851_, v_value_2852_, v_a_2854_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2859_, lean_object* v_decl_2860_, lean_object* v_type_2861_, lean_object* v_params_2862_, lean_object* v_value_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
uint8_t v_pu_boxed_2869_; lean_object* v_res_2870_; 
v_pu_boxed_2869_ = lean_unbox(v_pu_2859_);
v_res_2870_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2869_, v_decl_2860_, v_type_2861_, v_params_2862_, v_value_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2871_, lean_object* v_decl_2872_, lean_object* v_type_2873_, lean_object* v_value_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_params_2877_; lean_object* v___x_2878_; 
v_params_2877_ = lean_ctor_get(v_decl_2872_, 2);
lean_inc_ref(v_params_2877_);
v___x_2878_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2871_, v_decl_2872_, v_type_2873_, v_params_2877_, v_value_2874_, v_a_2875_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2879_, lean_object* v_decl_2880_, lean_object* v_type_2881_, lean_object* v_value_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
uint8_t v_pu_boxed_2885_; lean_object* v_res_2886_; 
v_pu_boxed_2885_ = lean_unbox(v_pu_2879_);
v_res_2886_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2885_, v_decl_2880_, v_type_2881_, v_value_2882_, v_a_2883_);
lean_dec(v_a_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2887_, lean_object* v_decl_2888_, lean_object* v_type_2889_, lean_object* v_value_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_params_2896_; lean_object* v___x_2897_; 
v_params_2896_ = lean_ctor_get(v_decl_2888_, 2);
lean_inc_ref(v_params_2896_);
v___x_2897_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2887_, v_decl_2888_, v_type_2889_, v_params_2896_, v_value_2890_, v_a_2892_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2898_, lean_object* v_decl_2899_, lean_object* v_type_2900_, lean_object* v_value_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
uint8_t v_pu_boxed_2907_; lean_object* v_res_2908_; 
v_pu_boxed_2907_ = lean_unbox(v_pu_2898_);
v_res_2908_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2907_, v_decl_2899_, v_type_2900_, v_value_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2909_, lean_object* v_decl_2910_, lean_object* v_value_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_params_2914_; lean_object* v_type_2915_; lean_object* v___x_2916_; 
v_params_2914_ = lean_ctor_get(v_decl_2910_, 2);
lean_inc_ref(v_params_2914_);
v_type_2915_ = lean_ctor_get(v_decl_2910_, 3);
lean_inc_ref(v_type_2915_);
v___x_2916_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2909_, v_decl_2910_, v_type_2915_, v_params_2914_, v_value_2911_, v_a_2912_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2917_, lean_object* v_decl_2918_, lean_object* v_value_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
uint8_t v_pu_boxed_2922_; lean_object* v_res_2923_; 
v_pu_boxed_2922_ = lean_unbox(v_pu_2917_);
v_res_2923_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2922_, v_decl_2918_, v_value_2919_, v_a_2920_);
lean_dec(v_a_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2924_, lean_object* v_decl_2925_, lean_object* v_value_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_params_2932_; lean_object* v_type_2933_; lean_object* v___x_2934_; 
v_params_2932_ = lean_ctor_get(v_decl_2925_, 2);
lean_inc_ref(v_params_2932_);
v_type_2933_ = lean_ctor_get(v_decl_2925_, 3);
lean_inc_ref(v_type_2933_);
v___x_2934_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2924_, v_decl_2925_, v_type_2933_, v_params_2932_, v_value_2926_, v_a_2928_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2935_, lean_object* v_decl_2936_, lean_object* v_value_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
uint8_t v_pu_boxed_2943_; lean_object* v_res_2944_; 
v_pu_boxed_2943_ = lean_unbox(v_pu_2935_);
v_res_2944_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2943_, v_decl_2936_, v_value_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2945_, lean_object* v_p_2946_, lean_object* v_inst_2947_, lean_object* v_____do__lift_2948_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_box(v_pu_2945_);
v___x_2950_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2950_, 0, v___x_2949_);
lean_closure_set(v___x_2950_, 1, v_p_2946_);
lean_closure_set(v___x_2950_, 2, v_____do__lift_2948_);
v___x_2951_ = lean_apply_2(v_inst_2947_, lean_box(0), v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2952_, lean_object* v_p_2953_, lean_object* v_inst_2954_, lean_object* v_____do__lift_2955_){
_start:
{
uint8_t v_pu_boxed_2956_; lean_object* v_res_2957_; 
v_pu_boxed_2956_ = lean_unbox(v_pu_2952_);
v_res_2957_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2956_, v_p_2953_, v_inst_2954_, v_____do__lift_2955_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2958_, uint8_t v_t_2959_, lean_object* v_type_2960_, lean_object* v_toPure_2961_, lean_object* v_____do__lift_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2958_, v_____do__lift_2962_, v_t_2959_, v_type_2960_);
v___x_2964_ = lean_apply_2(v_toPure_2961_, lean_box(0), v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2965_, lean_object* v_t_2966_, lean_object* v_type_2967_, lean_object* v_toPure_2968_, lean_object* v_____do__lift_2969_){
_start:
{
uint8_t v_pu_boxed_2970_; uint8_t v_t_boxed_2971_; lean_object* v_res_2972_; 
v_pu_boxed_2970_ = lean_unbox(v_pu_2965_);
v_t_boxed_2971_ = lean_unbox(v_t_2966_);
v_res_2972_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2970_, v_t_boxed_2971_, v_type_2967_, v_toPure_2968_, v_____do__lift_2969_);
lean_dec_ref(v_____do__lift_2969_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2973_, uint8_t v_t_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_p_2978_){
_start:
{
lean_object* v_toApplicative_2979_; lean_object* v_toBind_2980_; lean_object* v_type_2981_; lean_object* v_toPure_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___f_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_toApplicative_2979_ = lean_ctor_get(v_inst_2976_, 0);
lean_inc_ref(v_toApplicative_2979_);
v_toBind_2980_ = lean_ctor_get(v_inst_2976_, 1);
lean_inc_n(v_toBind_2980_, 2);
lean_dec_ref(v_inst_2976_);
v_type_2981_ = lean_ctor_get(v_p_2978_, 2);
lean_inc_ref(v_type_2981_);
v_toPure_2982_ = lean_ctor_get(v_toApplicative_2979_, 1);
lean_inc(v_toPure_2982_);
lean_dec_ref(v_toApplicative_2979_);
v___x_2983_ = lean_box(v_pu_2973_);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2984_, 0, v___x_2983_);
lean_closure_set(v___f_2984_, 1, v_p_2978_);
lean_closure_set(v___f_2984_, 2, v_inst_2975_);
v___x_2985_ = lean_box(v_pu_2973_);
v___x_2986_ = lean_box(v_t_2974_);
v___f_2987_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2987_, 0, v___x_2985_);
lean_closure_set(v___f_2987_, 1, v___x_2986_);
lean_closure_set(v___f_2987_, 2, v_type_2981_);
lean_closure_set(v___f_2987_, 3, v_toPure_2982_);
v___x_2988_ = lean_apply_4(v_toBind_2980_, lean_box(0), lean_box(0), v_inst_2977_, v___f_2987_);
v___x_2989_ = lean_apply_4(v_toBind_2980_, lean_box(0), lean_box(0), v___x_2988_, v___f_2984_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2990_, lean_object* v_t_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_p_2995_){
_start:
{
uint8_t v_pu_boxed_2996_; uint8_t v_t_boxed_2997_; lean_object* v_res_2998_; 
v_pu_boxed_2996_ = lean_unbox(v_pu_2990_);
v_t_boxed_2997_ = lean_unbox(v_t_2991_);
v_res_2998_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_2996_, v_t_boxed_2997_, v_inst_2992_, v_inst_2993_, v_inst_2994_, v_p_2995_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_2999_, uint8_t v_pu_3000_, uint8_t v_t_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_inst_3004_, lean_object* v_p_3005_){
_start:
{
lean_object* v_toApplicative_3006_; lean_object* v_toBind_3007_; lean_object* v_type_3008_; lean_object* v_toPure_3009_; lean_object* v___x_3010_; lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_toApplicative_3006_ = lean_ctor_get(v_inst_3003_, 0);
lean_inc_ref(v_toApplicative_3006_);
v_toBind_3007_ = lean_ctor_get(v_inst_3003_, 1);
lean_inc_n(v_toBind_3007_, 2);
lean_dec_ref(v_inst_3003_);
v_type_3008_ = lean_ctor_get(v_p_3005_, 2);
lean_inc_ref(v_type_3008_);
v_toPure_3009_ = lean_ctor_get(v_toApplicative_3006_, 1);
lean_inc(v_toPure_3009_);
lean_dec_ref(v_toApplicative_3006_);
v___x_3010_ = lean_box(v_pu_3000_);
v___f_3011_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3011_, 0, v___x_3010_);
lean_closure_set(v___f_3011_, 1, v_p_3005_);
lean_closure_set(v___f_3011_, 2, v_inst_3002_);
v___x_3012_ = lean_box(v_pu_3000_);
v___x_3013_ = lean_box(v_t_3001_);
v___f_3014_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3014_, 0, v___x_3012_);
lean_closure_set(v___f_3014_, 1, v___x_3013_);
lean_closure_set(v___f_3014_, 2, v_type_3008_);
lean_closure_set(v___f_3014_, 3, v_toPure_3009_);
v___x_3015_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v_inst_3004_, v___f_3014_);
v___x_3016_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3015_, v___f_3011_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3017_, lean_object* v_pu_3018_, lean_object* v_t_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_p_3023_){
_start:
{
uint8_t v_pu_boxed_3024_; uint8_t v_t_boxed_3025_; lean_object* v_res_3026_; 
v_pu_boxed_3024_ = lean_unbox(v_pu_3018_);
v_t_boxed_3025_ = lean_unbox(v_t_3019_);
v_res_3026_ = l_Lean_Compiler_LCNF_normParam(v_m_3017_, v_pu_boxed_3024_, v_t_boxed_3025_, v_inst_3020_, v_inst_3021_, v_inst_3022_, v_p_3023_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3027_, uint8_t v_t_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_ps_3032_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3033_ = lean_box(v_pu_3027_);
v___x_3034_ = lean_box(v_t_3028_);
lean_inc_ref(v_inst_3030_);
v___x_3035_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3035_, 0, lean_box(0));
lean_closure_set(v___x_3035_, 1, v___x_3033_);
lean_closure_set(v___x_3035_, 2, v___x_3034_);
lean_closure_set(v___x_3035_, 3, v_inst_3029_);
lean_closure_set(v___x_3035_, 4, v_inst_3030_);
lean_closure_set(v___x_3035_, 5, v_inst_3031_);
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3030_, v___x_3035_, v___x_3036_, v_ps_3032_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3038_, lean_object* v_t_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_ps_3043_){
_start:
{
uint8_t v_pu_boxed_3044_; uint8_t v_t_boxed_3045_; lean_object* v_res_3046_; 
v_pu_boxed_3044_ = lean_unbox(v_pu_3038_);
v_t_boxed_3045_ = lean_unbox(v_t_3039_);
v_res_3046_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3044_, v_t_boxed_3045_, v_inst_3040_, v_inst_3041_, v_inst_3042_, v_ps_3043_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3047_, uint8_t v_pu_3048_, uint8_t v_t_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_ps_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3048_, v_t_3049_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_ps_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3055_, lean_object* v_pu_3056_, lean_object* v_t_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_ps_3061_){
_start:
{
uint8_t v_pu_boxed_3062_; uint8_t v_t_boxed_3063_; lean_object* v_res_3064_; 
v_pu_boxed_3062_ = lean_unbox(v_pu_3056_);
v_t_boxed_3063_ = lean_unbox(v_t_3057_);
v_res_3064_ = l_Lean_Compiler_LCNF_normParams(v_m_3055_, v_pu_boxed_3062_, v_t_boxed_3063_, v_inst_3058_, v_inst_3059_, v_inst_3060_, v_ps_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3065_, lean_object* v_decl_3066_, lean_object* v_____do__lift_3067_, lean_object* v_inst_3068_, lean_object* v_____do__lift_3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_box(v_pu_3065_);
v___x_3071_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3071_, 0, v___x_3070_);
lean_closure_set(v___x_3071_, 1, v_decl_3066_);
lean_closure_set(v___x_3071_, 2, v_____do__lift_3067_);
lean_closure_set(v___x_3071_, 3, v_____do__lift_3069_);
v___x_3072_ = lean_apply_2(v_inst_3068_, lean_box(0), v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3073_, lean_object* v_decl_3074_, lean_object* v_____do__lift_3075_, lean_object* v_inst_3076_, lean_object* v_____do__lift_3077_){
_start:
{
uint8_t v_pu_boxed_3078_; lean_object* v_res_3079_; 
v_pu_boxed_3078_ = lean_unbox(v_pu_3073_);
v_res_3079_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3078_, v_decl_3074_, v_____do__lift_3075_, v_inst_3076_, v_____do__lift_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3080_, lean_object* v_value_3081_, uint8_t v_t_3082_, lean_object* v_toPure_3083_, lean_object* v_____do__lift_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3080_, v_____do__lift_3084_, v_value_3081_, v_t_3082_);
v___x_3086_ = lean_apply_2(v_toPure_3083_, lean_box(0), v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3087_, lean_object* v_value_3088_, lean_object* v_t_3089_, lean_object* v_toPure_3090_, lean_object* v_____do__lift_3091_){
_start:
{
uint8_t v_pu_boxed_3092_; uint8_t v_t_boxed_3093_; lean_object* v_res_3094_; 
v_pu_boxed_3092_ = lean_unbox(v_pu_3087_);
v_t_boxed_3093_ = lean_unbox(v_t_3089_);
v_res_3094_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3092_, v_value_3088_, v_t_boxed_3093_, v_toPure_3090_, v_____do__lift_3091_);
lean_dec_ref(v_____do__lift_3091_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3095_, lean_object* v_decl_3096_, lean_object* v_inst_3097_, lean_object* v_value_3098_, uint8_t v_t_3099_, lean_object* v_toPure_3100_, lean_object* v_toBind_3101_, lean_object* v_inst_3102_, lean_object* v_____do__lift_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3104_ = lean_box(v_pu_3095_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3105_, 0, v___x_3104_);
lean_closure_set(v___f_3105_, 1, v_decl_3096_);
lean_closure_set(v___f_3105_, 2, v_____do__lift_3103_);
lean_closure_set(v___f_3105_, 3, v_inst_3097_);
v___x_3106_ = lean_box(v_pu_3095_);
v___x_3107_ = lean_box(v_t_3099_);
v___f_3108_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3108_, 0, v___x_3106_);
lean_closure_set(v___f_3108_, 1, v_value_3098_);
lean_closure_set(v___f_3108_, 2, v___x_3107_);
lean_closure_set(v___f_3108_, 3, v_toPure_3100_);
lean_inc(v_toBind_3101_);
v___x_3109_ = lean_apply_4(v_toBind_3101_, lean_box(0), lean_box(0), v_inst_3102_, v___f_3108_);
v___x_3110_ = lean_apply_4(v_toBind_3101_, lean_box(0), lean_box(0), v___x_3109_, v___f_3105_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3111_, lean_object* v_decl_3112_, lean_object* v_inst_3113_, lean_object* v_value_3114_, lean_object* v_t_3115_, lean_object* v_toPure_3116_, lean_object* v_toBind_3117_, lean_object* v_inst_3118_, lean_object* v_____do__lift_3119_){
_start:
{
uint8_t v_pu_boxed_3120_; uint8_t v_t_boxed_3121_; lean_object* v_res_3122_; 
v_pu_boxed_3120_ = lean_unbox(v_pu_3111_);
v_t_boxed_3121_ = lean_unbox(v_t_3115_);
v_res_3122_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3120_, v_decl_3112_, v_inst_3113_, v_value_3114_, v_t_boxed_3121_, v_toPure_3116_, v_toBind_3117_, v_inst_3118_, v_____do__lift_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3123_, uint8_t v_t_3124_, lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_decl_3128_){
_start:
{
lean_object* v_toApplicative_3129_; lean_object* v_toBind_3130_; lean_object* v_type_3131_; lean_object* v_value_3132_; lean_object* v_toPure_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___f_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___f_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_toApplicative_3129_ = lean_ctor_get(v_inst_3126_, 0);
lean_inc_ref(v_toApplicative_3129_);
v_toBind_3130_ = lean_ctor_get(v_inst_3126_, 1);
lean_inc_n(v_toBind_3130_, 3);
lean_dec_ref(v_inst_3126_);
v_type_3131_ = lean_ctor_get(v_decl_3128_, 2);
lean_inc_ref(v_type_3131_);
v_value_3132_ = lean_ctor_get(v_decl_3128_, 3);
lean_inc(v_value_3132_);
v_toPure_3133_ = lean_ctor_get(v_toApplicative_3129_, 1);
lean_inc_n(v_toPure_3133_, 2);
lean_dec_ref(v_toApplicative_3129_);
v___x_3134_ = lean_box(v_pu_3123_);
v___x_3135_ = lean_box(v_t_3124_);
lean_inc(v_inst_3127_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3136_, 0, v___x_3134_);
lean_closure_set(v___f_3136_, 1, v_decl_3128_);
lean_closure_set(v___f_3136_, 2, v_inst_3125_);
lean_closure_set(v___f_3136_, 3, v_value_3132_);
lean_closure_set(v___f_3136_, 4, v___x_3135_);
lean_closure_set(v___f_3136_, 5, v_toPure_3133_);
lean_closure_set(v___f_3136_, 6, v_toBind_3130_);
lean_closure_set(v___f_3136_, 7, v_inst_3127_);
v___x_3137_ = lean_box(v_pu_3123_);
v___x_3138_ = lean_box(v_t_3124_);
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3139_, 0, v___x_3137_);
lean_closure_set(v___f_3139_, 1, v___x_3138_);
lean_closure_set(v___f_3139_, 2, v_type_3131_);
lean_closure_set(v___f_3139_, 3, v_toPure_3133_);
v___x_3140_ = lean_apply_4(v_toBind_3130_, lean_box(0), lean_box(0), v_inst_3127_, v___f_3139_);
v___x_3141_ = lean_apply_4(v_toBind_3130_, lean_box(0), lean_box(0), v___x_3140_, v___f_3136_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3142_, lean_object* v_t_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_decl_3147_){
_start:
{
uint8_t v_pu_boxed_3148_; uint8_t v_t_boxed_3149_; lean_object* v_res_3150_; 
v_pu_boxed_3148_ = lean_unbox(v_pu_3142_);
v_t_boxed_3149_ = lean_unbox(v_t_3143_);
v_res_3150_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3148_, v_t_boxed_3149_, v_inst_3144_, v_inst_3145_, v_inst_3146_, v_decl_3147_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3151_, uint8_t v_pu_3152_, uint8_t v_t_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_decl_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3152_, v_t_3153_, v_inst_3154_, v_inst_3155_, v_inst_3156_, v_decl_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3159_, lean_object* v_pu_3160_, lean_object* v_t_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_decl_3165_){
_start:
{
uint8_t v_pu_boxed_3166_; uint8_t v_t_boxed_3167_; lean_object* v_res_3168_; 
v_pu_boxed_3166_ = lean_unbox(v_pu_3160_);
v_t_boxed_3167_ = lean_unbox(v_t_3161_);
v_res_3168_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3159_, v_pu_boxed_3166_, v_t_boxed_3167_, v_inst_3162_, v_inst_3163_, v_inst_3164_, v_decl_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg(){
_start:
{
lean_object* v___x_3170_; lean_object* v_toApplicative_3171_; lean_object* v_toFunctor_3172_; lean_object* v_toSeq_3173_; lean_object* v_toSeqLeft_3174_; lean_object* v_toSeqRight_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___f_3179_; lean_object* v___x_3180_; lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v_toApplicative_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3215_; 
v___x_3170_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3171_ = lean_ctor_get(v___x_3170_, 0);
v_toFunctor_3172_ = lean_ctor_get(v_toApplicative_3171_, 0);
v_toSeq_3173_ = lean_ctor_get(v_toApplicative_3171_, 2);
v_toSeqLeft_3174_ = lean_ctor_get(v_toApplicative_3171_, 3);
v_toSeqRight_3175_ = lean_ctor_get(v_toApplicative_3171_, 4);
v___f_3176_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3177_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3172_, 2);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toFunctor_3172_);
v___f_3179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3179_, 0, v_toFunctor_3172_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___f_3178_);
lean_ctor_set(v___x_3180_, 1, v___f_3179_);
lean_inc(v_toSeqRight_3175_);
v___f_3181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3181_, 0, v_toSeqRight_3175_);
lean_inc(v_toSeqLeft_3174_);
v___f_3182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3182_, 0, v_toSeqLeft_3174_);
lean_inc(v_toSeq_3173_);
v___f_3183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3183_, 0, v_toSeq_3173_);
v___x_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3180_);
lean_ctor_set(v___x_3184_, 1, v___f_3176_);
lean_ctor_set(v___x_3184_, 2, v___f_3183_);
lean_ctor_set(v___x_3184_, 3, v___f_3182_);
lean_ctor_set(v___x_3184_, 4, v___f_3181_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v___f_3177_);
v___x_3186_ = l_StateRefT_x27_instMonad___redArg(v___x_3185_);
v_toApplicative_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v___x_3186_, 1);
lean_dec(v_unused_3216_);
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3215_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_toApplicative_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3215_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_toFunctor_3191_; lean_object* v_toSeq_3192_; lean_object* v_toSeqLeft_3193_; lean_object* v_toSeqRight_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3213_; 
v_toFunctor_3191_ = lean_ctor_get(v_toApplicative_3187_, 0);
v_toSeq_3192_ = lean_ctor_get(v_toApplicative_3187_, 2);
v_toSeqLeft_3193_ = lean_ctor_get(v_toApplicative_3187_, 3);
v_toSeqRight_3194_ = lean_ctor_get(v_toApplicative_3187_, 4);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_toApplicative_3187_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v_toApplicative_3187_, 1);
lean_dec(v_unused_3214_);
v___x_3196_ = v_toApplicative_3187_;
v_isShared_3197_ = v_isSharedCheck_3213_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_toSeqRight_3194_);
lean_inc(v_toSeqLeft_3193_);
lean_inc(v_toSeq_3192_);
lean_inc(v_toFunctor_3191_);
lean_dec(v_toApplicative_3187_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3213_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___f_3205_; lean_object* v___x_3207_; 
v___f_3198_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3199_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3191_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toFunctor_3191_);
v___f_3201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3201_, 0, v_toFunctor_3191_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___f_3200_);
lean_ctor_set(v___x_3202_, 1, v___f_3201_);
v___f_3203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3203_, 0, v_toSeqRight_3194_);
v___f_3204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3204_, 0, v_toSeqLeft_3193_);
v___f_3205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3205_, 0, v_toSeq_3192_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 4, v___f_3203_);
lean_ctor_set(v___x_3196_, 3, v___f_3204_);
lean_ctor_set(v___x_3196_, 2, v___f_3205_);
lean_ctor_set(v___x_3196_, 1, v___f_3198_);
lean_ctor_set(v___x_3196_, 0, v___x_3202_);
v___x_3207_ = v___x_3196_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___f_3198_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v___f_3205_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v___f_3204_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v___f_3203_);
v___x_3207_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 1, v___f_3199_);
lean_ctor_set(v___x_3189_, 0, v___x_3207_);
v___x_3209_ = v___x_3189_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___f_3199_);
v___x_3209_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3210_, 0, lean_box(0));
lean_closure_set(v___x_3210_, 1, lean_box(0));
lean_closure_set(v___x_3210_, 2, v___x_3209_);
return v___x_3210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object* v___dummy_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v_res_3218_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0(void){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3220_, uint8_t v_t_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0, &l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3223_, lean_object* v_t_3224_){
_start:
{
uint8_t v_pu_boxed_3225_; uint8_t v_t_boxed_3226_; lean_object* v_res_3227_; 
v_pu_boxed_3225_ = lean_unbox(v_pu_3223_);
v_t_boxed_3226_ = lean_unbox(v_t_3224_);
v_res_3227_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3225_, v_t_boxed_3226_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3228_, lean_object* v_inst_3229_, lean_object* v_result_3230_, lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_result_3230_) == 0)
{
lean_object* v_fvarId_3232_; lean_object* v___x_3233_; 
lean_dec(v_inst_3229_);
v_fvarId_3232_ = lean_ctor_get(v_result_3230_, 0);
lean_inc(v_fvarId_3232_);
lean_dec_ref_known(v_result_3230_, 1);
v___x_3233_ = lean_apply_1(v_x_3231_, v_fvarId_3232_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec(v_x_3231_);
v___x_3234_ = lean_box(v_pu_3228_);
v___x_3235_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3235_, 0, v___x_3234_);
v___x_3236_ = lean_apply_2(v_inst_3229_, lean_box(0), v___x_3235_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3237_, lean_object* v_inst_3238_, lean_object* v_result_3239_, lean_object* v_x_3240_){
_start:
{
uint8_t v_pu_boxed_3241_; lean_object* v_res_3242_; 
v_pu_boxed_3241_ = lean_unbox(v_pu_3237_);
v_res_3242_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3241_, v_inst_3238_, v_result_3239_, v_x_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3243_, uint8_t v_pu_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_result_3247_, lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_result_3247_) == 0)
{
lean_object* v_fvarId_3249_; lean_object* v___x_3250_; 
lean_dec(v_inst_3245_);
v_fvarId_3249_ = lean_ctor_get(v_result_3247_, 0);
lean_inc(v_fvarId_3249_);
lean_dec_ref_known(v_result_3247_, 1);
v___x_3250_ = lean_apply_1(v_x_3248_, v_fvarId_3249_);
return v___x_3250_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_x_3248_);
v___x_3251_ = lean_box(v_pu_3244_);
v___x_3252_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3252_, 0, v___x_3251_);
v___x_3253_ = lean_apply_2(v_inst_3245_, lean_box(0), v___x_3252_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3254_, lean_object* v_pu_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_result_3258_, lean_object* v_x_3259_){
_start:
{
uint8_t v_pu_boxed_3260_; lean_object* v_res_3261_; 
v_pu_boxed_3260_ = lean_unbox(v_pu_3255_);
v_res_3261_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3254_, v_pu_boxed_3260_, v_inst_3256_, v_inst_3257_, v_result_3258_, v_x_3259_);
lean_dec_ref(v_inst_3257_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3262_, uint8_t v_t_3263_, lean_object* v_args_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3262_, v___y_3265_, v_args_3264_, v_t_3263_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3269_, lean_object* v_t_3270_, lean_object* v_args_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v_pu_boxed_3274_; uint8_t v_t_boxed_3275_; lean_object* v_res_3276_; 
v_pu_boxed_3274_ = lean_unbox(v_pu_3269_);
v_t_boxed_3275_ = lean_unbox(v_t_3270_);
v_res_3276_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3274_, v_t_boxed_3275_, v_args_3271_, v___y_3272_);
lean_dec_ref(v___y_3272_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3277_, uint8_t v_t_3278_, lean_object* v_i_3279_, lean_object* v_as_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = lean_array_get_size(v_as_3280_);
v___x_3285_ = lean_nat_dec_lt(v_i_3279_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
lean_dec(v_i_3279_);
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_as_3280_);
return v___x_3286_;
}
else
{
lean_object* v_a_3287_; lean_object* v_type_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_a_3287_ = lean_array_fget_borrowed(v_as_3280_, v_i_3279_);
v_type_3288_ = lean_ctor_get(v_a_3287_, 2);
lean_inc_ref(v_type_3288_);
v___x_3289_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3277_, v___y_3281_, v_t_3278_, v_type_3288_);
lean_inc(v_a_3287_);
v___x_3290_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3277_, v_a_3287_, v___x_3289_, v___y_3282_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; size_t v___x_3292_; size_t v___x_3293_; uint8_t v___x_3294_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v___x_3292_ = lean_ptr_addr(v_a_3287_);
v___x_3293_ = lean_ptr_addr(v_a_3291_);
v___x_3294_ = lean_usize_dec_eq(v___x_3292_, v___x_3293_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_unsigned_to_nat(1u);
v___x_3296_ = lean_nat_add(v_i_3279_, v___x_3295_);
v___x_3297_ = lean_array_fset(v_as_3280_, v_i_3279_, v_a_3291_);
lean_dec(v_i_3279_);
v_i_3279_ = v___x_3296_;
v_as_3280_ = v___x_3297_;
goto _start;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_a_3291_);
v___x_3299_ = lean_unsigned_to_nat(1u);
v___x_3300_ = lean_nat_add(v_i_3279_, v___x_3299_);
lean_dec(v_i_3279_);
v_i_3279_ = v___x_3300_;
goto _start;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_as_3280_);
lean_dec(v_i_3279_);
v_a_3302_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3290_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3290_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3310_, lean_object* v_t_3311_, lean_object* v_i_3312_, lean_object* v_as_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
uint8_t v_pu_boxed_3317_; uint8_t v_t_boxed_3318_; lean_object* v_res_3319_; 
v_pu_boxed_3317_ = lean_unbox(v_pu_3310_);
v_t_boxed_3318_ = lean_unbox(v_t_3311_);
v_res_3319_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3317_, v_t_boxed_3318_, v_i_3312_, v_as_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3320_, uint8_t v_t_3321_, lean_object* v_ps_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3320_, v_t_3321_, v___x_3329_, v_ps_3322_, v___y_3323_, v___y_3325_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3331_, lean_object* v_t_3332_, lean_object* v_ps_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v_pu_boxed_3340_; uint8_t v_t_boxed_3341_; lean_object* v_res_3342_; 
v_pu_boxed_3340_ = lean_unbox(v_pu_3331_);
v_t_boxed_3341_ = lean_unbox(v_t_3332_);
v_res_3342_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3340_, v_t_boxed_3341_, v_ps_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3343_, uint8_t v_t_3344_, lean_object* v_decl_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_type_3349_; lean_object* v_value_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_type_3349_ = lean_ctor_get(v_decl_3345_, 2);
v_value_3350_ = lean_ctor_get(v_decl_3345_, 3);
lean_inc_ref(v_type_3349_);
v___x_3351_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3343_, v___y_3346_, v_t_3344_, v_type_3349_);
lean_inc(v_value_3350_);
v___x_3352_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3343_, v___y_3346_, v_value_3350_, v_t_3344_);
v___x_3353_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3343_, v_decl_3345_, v___x_3351_, v___x_3352_, v___y_3347_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3354_, lean_object* v_t_3355_, lean_object* v_decl_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
uint8_t v_pu_boxed_3360_; uint8_t v_t_boxed_3361_; lean_object* v_res_3362_; 
v_pu_boxed_3360_ = lean_unbox(v_pu_3354_);
v_t_boxed_3361_ = lean_unbox(v_t_3355_);
v_res_3362_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3360_, v_t_boxed_3361_, v_decl_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3363_, uint8_t v_t_3364_, lean_object* v_i_3365_, lean_object* v_as_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = lean_array_get_size(v_as_3366_);
v___x_3374_ = lean_nat_dec_lt(v_i_3365_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
lean_dec(v_i_3365_);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_as_3366_);
return v___x_3375_;
}
else
{
lean_object* v_a_3376_; lean_object* v_a_3378_; 
v_a_3376_ = lean_array_fget_borrowed(v_as_3366_, v_i_3365_);
switch(lean_obj_tag(v_a_3376_))
{
case 0:
{
lean_object* v_params_3389_; lean_object* v_code_3390_; lean_object* v___x_3391_; 
v_params_3389_ = lean_ctor_get(v_a_3376_, 1);
v_code_3390_ = lean_ctor_get(v_a_3376_, 2);
lean_inc_ref(v_params_3389_);
v___x_3391_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3363_, v_t_3364_, v_params_3389_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc_ref(v_code_3390_);
v___x_3393_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3363_, v_t_3364_, v_code_3390_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
lean_inc_ref(v_a_3376_);
v___x_3395_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3363_, v_a_3376_, v_a_3392_, v_a_3394_);
v_a_3378_ = v___x_3395_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v_a_3392_);
lean_dec_ref(v_as_3366_);
lean_dec(v_i_3365_);
v_a_3396_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3393_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3393_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_as_3366_);
lean_dec(v_i_3365_);
v_a_3404_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3391_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3391_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
case 1:
{
lean_object* v_code_3412_; lean_object* v___x_3413_; 
v_code_3412_ = lean_ctor_get(v_a_3376_, 1);
lean_inc_ref(v_code_3412_);
v___x_3413_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3363_, v_t_3364_, v_code_3412_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
lean_inc_ref(v_a_3376_);
v___x_3415_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3376_, v_a_3414_);
v_a_3378_ = v___x_3415_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_as_3366_);
lean_dec(v_i_3365_);
v_a_3416_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3413_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3413_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
default: 
{
lean_object* v_code_3424_; lean_object* v___x_3425_; 
v_code_3424_ = lean_ctor_get(v_a_3376_, 0);
lean_inc_ref(v_code_3424_);
v___x_3425_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3363_, v_t_3364_, v_code_3424_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
lean_inc_ref(v_a_3376_);
v___x_3427_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3376_, v_a_3426_);
v_a_3378_ = v___x_3427_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref(v_as_3366_);
lean_dec(v_i_3365_);
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
}
v___jp_3377_:
{
size_t v___x_3379_; size_t v___x_3380_; uint8_t v___x_3381_; 
v___x_3379_ = lean_ptr_addr(v_a_3376_);
v___x_3380_ = lean_ptr_addr(v_a_3378_);
v___x_3381_ = lean_usize_dec_eq(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = lean_unsigned_to_nat(1u);
v___x_3383_ = lean_nat_add(v_i_3365_, v___x_3382_);
v___x_3384_ = lean_array_fset(v_as_3366_, v_i_3365_, v_a_3378_);
lean_dec(v_i_3365_);
v_i_3365_ = v___x_3383_;
v_as_3366_ = v___x_3384_;
goto _start;
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec_ref(v_a_3378_);
v___x_3386_ = lean_unsigned_to_nat(1u);
v___x_3387_ = lean_nat_add(v_i_3365_, v___x_3386_);
lean_dec(v_i_3365_);
v_i_3365_ = v___x_3387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3436_, uint8_t v_t_3437_, lean_object* v_code_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
switch(lean_obj_tag(v_code_3438_))
{
case 0:
{
lean_object* v_decl_3445_; lean_object* v_k_3446_; lean_object* v___x_3447_; 
v_decl_3445_ = lean_ctor_get(v_code_3438_, 0);
v_k_3446_ = lean_ctor_get(v_code_3438_, 1);
lean_inc_ref(v_decl_3445_);
v___x_3447_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3436_, v_t_3437_, v_decl_3445_, v_a_3439_, v_a_3441_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
lean_inc_ref(v_k_3446_);
v___x_3449_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_3446_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3487_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3487_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3487_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
size_t v___x_3454_; size_t v___x_3455_; uint8_t v___x_3456_; 
v___x_3454_ = lean_ptr_addr(v_k_3446_);
v___x_3455_ = lean_ptr_addr(v_a_3450_);
v___x_3456_ = lean_usize_dec_eq(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3467_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3468_);
v___x_3458_ = v_code_3438_;
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_code_3438_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_a_3450_);
lean_ctor_set(v___x_3458_, 0, v_a_3448_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3448_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3450_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3461_);
v___x_3463_ = v___x_3452_;
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
size_t v___x_3469_; size_t v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = lean_ptr_addr(v_decl_3445_);
v___x_3470_ = lean_ptr_addr(v_a_3448_);
v___x_3471_ = lean_usize_dec_eq(v___x_3469_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3481_; 
v_isSharedCheck_3481_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; 
v_unused_3482_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3483_);
v___x_3473_ = v_code_3438_;
v_isShared_3474_ = v_isSharedCheck_3481_;
goto v_resetjp_3472_;
}
else
{
lean_dec(v_code_3438_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3481_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 1, v_a_3450_);
lean_ctor_set(v___x_3473_, 0, v_a_3448_);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3448_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_a_3450_);
v___x_3476_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3476_);
v___x_3478_ = v___x_3452_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
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
else
{
lean_object* v___x_3485_; 
lean_dec(v_a_3450_);
lean_dec(v_a_3448_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v_code_3438_);
v___x_3485_ = v___x_3452_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_code_3438_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
else
{
lean_dec(v_a_3448_);
lean_dec_ref_known(v_code_3438_, 2);
return v___x_3449_;
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref_known(v_code_3438_, 2);
v_a_3488_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3447_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3447_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
case 1:
{
lean_object* v_decl_3496_; lean_object* v_k_3497_; lean_object* v___x_3498_; 
v_decl_3496_ = lean_ctor_get(v_code_3438_, 0);
v_k_3497_ = lean_ctor_get(v_code_3438_, 1);
lean_inc_ref(v_decl_3496_);
v___x_3498_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3436_, v_t_3437_, v_decl_3496_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
lean_inc_ref(v_k_3497_);
v___x_3500_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_3497_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3538_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3538_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3538_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
size_t v___x_3505_; size_t v___x_3506_; uint8_t v___x_3507_; 
v___x_3505_ = lean_ptr_addr(v_k_3497_);
v___x_3506_ = lean_ptr_addr(v_a_3501_);
v___x_3507_ = lean_usize_dec_eq(v___x_3505_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3517_; 
v_isSharedCheck_3517_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; lean_object* v_unused_3519_; 
v_unused_3518_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3519_);
v___x_3509_ = v_code_3438_;
v_isShared_3510_ = v_isSharedCheck_3517_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v_code_3438_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3517_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v_a_3501_);
lean_ctor_set(v___x_3509_, 0, v_a_3499_);
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_a_3501_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3512_);
v___x_3514_ = v___x_3503_;
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
size_t v___x_3520_; size_t v___x_3521_; uint8_t v___x_3522_; 
v___x_3520_ = lean_ptr_addr(v_decl_3496_);
v___x_3521_ = lean_ptr_addr(v_a_3499_);
v___x_3522_ = lean_usize_dec_eq(v___x_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3532_; 
v_isSharedCheck_3532_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; lean_object* v_unused_3534_; 
v_unused_3533_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3534_);
v___x_3524_ = v_code_3438_;
v_isShared_3525_ = v_isSharedCheck_3532_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v_code_3438_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3532_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v_a_3501_);
lean_ctor_set(v___x_3524_, 0, v_a_3499_);
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_a_3501_);
v___x_3527_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3527_);
v___x_3529_ = v___x_3503_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
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
else
{
lean_object* v___x_3536_; 
lean_dec(v_a_3501_);
lean_dec(v_a_3499_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v_code_3438_);
v___x_3536_ = v___x_3503_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_code_3438_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
else
{
lean_dec(v_a_3499_);
lean_dec_ref_known(v_code_3438_, 2);
return v___x_3500_;
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref_known(v_code_3438_, 2);
v_a_3539_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3498_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3498_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
case 2:
{
lean_object* v_decl_3547_; lean_object* v_k_3548_; lean_object* v___x_3549_; 
v_decl_3547_ = lean_ctor_get(v_code_3438_, 0);
v_k_3548_ = lean_ctor_get(v_code_3438_, 1);
lean_inc_ref(v_decl_3547_);
v___x_3549_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3436_, v_t_3437_, v_decl_3547_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
lean_inc_ref(v_k_3548_);
v___x_3551_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_3548_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3589_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3589_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3589_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
size_t v___x_3556_; size_t v___x_3557_; uint8_t v___x_3558_; 
v___x_3556_ = lean_ptr_addr(v_k_3548_);
v___x_3557_ = lean_ptr_addr(v_a_3552_);
v___x_3558_ = lean_usize_dec_eq(v___x_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3568_; 
v_isSharedCheck_3568_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3569_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3570_);
v___x_3560_ = v_code_3438_;
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v_code_3438_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v_a_3552_);
lean_ctor_set(v___x_3560_, 0, v_a_3550_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3550_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3552_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3563_);
v___x_3565_ = v___x_3554_;
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
size_t v___x_3571_; size_t v___x_3572_; uint8_t v___x_3573_; 
v___x_3571_ = lean_ptr_addr(v_decl_3547_);
v___x_3572_ = lean_ptr_addr(v_a_3550_);
v___x_3573_ = lean_usize_dec_eq(v___x_3571_, v___x_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3583_; 
v_isSharedCheck_3583_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; lean_object* v_unused_3585_; 
v_unused_3584_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3584_);
v_unused_3585_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3585_);
v___x_3575_ = v_code_3438_;
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
else
{
lean_dec(v_code_3438_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 1, v_a_3552_);
lean_ctor_set(v___x_3575_, 0, v_a_3550_);
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3550_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_a_3552_);
v___x_3578_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3580_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3578_);
v___x_3580_ = v___x_3554_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
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
else
{
lean_object* v___x_3587_; 
lean_dec(v_a_3552_);
lean_dec(v_a_3550_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_code_3438_);
v___x_3587_ = v___x_3554_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_code_3438_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
else
{
lean_dec(v_a_3550_);
lean_dec_ref_known(v_code_3438_, 2);
return v___x_3551_;
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref_known(v_code_3438_, 2);
v_a_3590_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3549_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3549_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
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
case 3:
{
lean_object* v_fvarId_3598_; lean_object* v_args_3599_; lean_object* v___x_3600_; 
v_fvarId_3598_ = lean_ctor_get(v_code_3438_, 0);
v_args_3599_ = lean_ctor_get(v_code_3438_, 1);
lean_inc(v_fvarId_3598_);
v___x_3600_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_3598_, v_t_3437_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_fvarId_3601_; lean_object* v___x_3602_; 
v_fvarId_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_fvarId_3601_);
lean_dec_ref_known(v___x_3600_, 1);
lean_inc_ref(v_args_3599_);
v___x_3602_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3436_, v_t_3437_, v_args_3599_, v_a_3439_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3628_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3628_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3628_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
uint8_t v___y_3608_; uint8_t v___x_3624_; 
v___x_3624_ = l_Lean_instBEqFVarId_beq(v_fvarId_3598_, v_fvarId_3601_);
if (v___x_3624_ == 0)
{
v___y_3608_ = v___x_3624_;
goto v___jp_3607_;
}
else
{
size_t v___x_3625_; size_t v___x_3626_; uint8_t v___x_3627_; 
v___x_3625_ = lean_ptr_addr(v_args_3599_);
v___x_3626_ = lean_ptr_addr(v_a_3603_);
v___x_3627_ = lean_usize_dec_eq(v___x_3625_, v___x_3626_);
v___y_3608_ = v___x_3627_;
goto v___jp_3607_;
}
v___jp_3607_:
{
if (v___y_3608_ == 0)
{
lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3618_; 
v_isSharedCheck_3618_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; lean_object* v_unused_3620_; 
v_unused_3619_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3619_);
v_unused_3620_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3620_);
v___x_3610_ = v_code_3438_;
v_isShared_3611_ = v_isSharedCheck_3618_;
goto v_resetjp_3609_;
}
else
{
lean_dec(v_code_3438_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3618_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 1, v_a_3603_);
lean_ctor_set(v___x_3610_, 0, v_fvarId_3601_);
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_fvarId_3601_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3603_);
v___x_3613_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3613_);
v___x_3615_ = v___x_3605_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v___x_3622_; 
lean_dec(v_a_3603_);
lean_dec(v_fvarId_3601_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v_code_3438_);
v___x_3622_ = v___x_3605_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_code_3438_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v_fvarId_3601_);
lean_dec_ref_known(v_code_3438_, 2);
v_a_3629_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3602_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3602_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_object* v___x_3637_; 
lean_dec_ref_known(v_code_3438_, 2);
v___x_3637_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3637_;
}
}
case 4:
{
lean_object* v_cases_3638_; lean_object* v_typeName_3639_; lean_object* v_resultType_3640_; lean_object* v_discr_3641_; lean_object* v_alts_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3687_; 
v_cases_3638_ = lean_ctor_get(v_code_3438_, 0);
lean_inc_ref(v_cases_3638_);
v_typeName_3639_ = lean_ctor_get(v_cases_3638_, 0);
v_resultType_3640_ = lean_ctor_get(v_cases_3638_, 1);
v_discr_3641_ = lean_ctor_get(v_cases_3638_, 2);
v_alts_3642_ = lean_ctor_get(v_cases_3638_, 3);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_cases_3638_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3644_ = v_cases_3638_;
v_isShared_3645_ = v_isSharedCheck_3687_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_alts_3642_);
lean_inc(v_discr_3641_);
lean_inc(v_resultType_3640_);
lean_inc(v_typeName_3639_);
lean_dec(v_cases_3638_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3687_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_inc_ref(v_resultType_3640_);
v___x_3646_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3436_, v_a_3439_, v_t_3437_, v_resultType_3640_);
lean_inc(v_discr_3641_);
v___x_3647_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_discr_3641_, v_t_3437_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_fvarId_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3685_; 
v_fvarId_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3685_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_fvarId_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3685_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3642_);
v___x_3653_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3436_, v_t_3437_, v___x_3652_, v_alts_3642_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3676_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3676_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3676_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
size_t v___x_3668_; size_t v___x_3669_; uint8_t v___x_3670_; 
v___x_3668_ = lean_ptr_addr(v_alts_3642_);
lean_dec_ref(v_alts_3642_);
v___x_3669_ = lean_ptr_addr(v_a_3654_);
v___x_3670_ = lean_usize_dec_eq(v___x_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_dec(v_discr_3641_);
lean_dec_ref(v_resultType_3640_);
lean_dec_ref_known(v_code_3438_, 1);
goto v___jp_3658_;
}
else
{
size_t v___x_3671_; size_t v___x_3672_; uint8_t v___x_3673_; 
v___x_3671_ = lean_ptr_addr(v_resultType_3640_);
lean_dec_ref(v_resultType_3640_);
v___x_3672_ = lean_ptr_addr(v___x_3646_);
v___x_3673_ = lean_usize_dec_eq(v___x_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_dec(v_discr_3641_);
lean_dec_ref_known(v_code_3438_, 1);
goto v___jp_3658_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = l_Lean_instBEqFVarId_beq(v_discr_3641_, v_fvarId_3648_);
lean_dec(v_discr_3641_);
if (v___x_3674_ == 0)
{
lean_dec_ref_known(v_code_3438_, 1);
goto v___jp_3658_;
}
else
{
lean_object* v___x_3675_; 
lean_del_object(v___x_3656_);
lean_dec(v_a_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_fvarId_3648_);
lean_dec_ref(v___x_3646_);
lean_del_object(v___x_3644_);
lean_dec(v_typeName_3639_);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v_code_3438_);
return v___x_3675_;
}
}
}
v___jp_3658_:
{
lean_object* v___x_3660_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 3, v_a_3654_);
lean_ctor_set(v___x_3644_, 2, v_fvarId_3648_);
lean_ctor_set(v___x_3644_, 1, v___x_3646_);
v___x_3660_ = v___x_3644_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_typeName_3639_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_fvarId_3648_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_a_3654_);
v___x_3660_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3662_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 4);
lean_ctor_set(v___x_3650_, 0, v___x_3660_);
v___x_3662_ = v___x_3650_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3662_);
v___x_3664_ = v___x_3656_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
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
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_del_object(v___x_3650_);
lean_dec(v_fvarId_3648_);
lean_dec_ref(v___x_3646_);
lean_del_object(v___x_3644_);
lean_dec_ref(v_alts_3642_);
lean_dec(v_discr_3641_);
lean_dec_ref(v_resultType_3640_);
lean_dec(v_typeName_3639_);
lean_dec_ref_known(v_code_3438_, 1);
v_a_3677_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3653_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3653_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
else
{
lean_object* v___x_3686_; 
lean_dec_ref(v___x_3646_);
lean_del_object(v___x_3644_);
lean_dec_ref(v_alts_3642_);
lean_dec(v_discr_3641_);
lean_dec_ref(v_resultType_3640_);
lean_dec(v_typeName_3639_);
lean_dec_ref_known(v_code_3438_, 1);
v___x_3686_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3686_;
}
}
}
case 5:
{
lean_object* v_fvarId_3688_; lean_object* v___x_3689_; 
v_fvarId_3688_ = lean_ctor_get(v_code_3438_, 0);
lean_inc(v_fvarId_3688_);
v___x_3689_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_3688_, v_t_3437_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_fvarId_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3709_; 
v_fvarId_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3709_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_fvarId_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3709_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
uint8_t v___x_3694_; 
v___x_3694_ = l_Lean_instBEqFVarId_beq(v_fvarId_3688_, v_fvarId_3690_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3704_; 
v_isSharedCheck_3704_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3704_ == 0)
{
lean_object* v_unused_3705_; 
v_unused_3705_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3705_);
v___x_3696_ = v_code_3438_;
v_isShared_3697_ = v_isSharedCheck_3704_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v_code_3438_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3704_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v_fvarId_3690_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_fvarId_3690_);
v___x_3699_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3701_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3699_);
v___x_3701_ = v___x_3692_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v___x_3707_; 
lean_dec(v_fvarId_3690_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v_code_3438_);
v___x_3707_ = v___x_3692_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_code_3438_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
else
{
lean_object* v___x_3710_; 
lean_dec_ref_known(v_code_3438_, 1);
v___x_3710_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3710_;
}
}
case 6:
{
lean_object* v_type_3711_; lean_object* v___x_3712_; size_t v___x_3713_; size_t v___x_3714_; uint8_t v___x_3715_; 
v_type_3711_ = lean_ctor_get(v_code_3438_, 0);
lean_inc_ref(v_type_3711_);
v___x_3712_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3436_, v_a_3439_, v_t_3437_, v_type_3711_);
v___x_3713_ = lean_ptr_addr(v_type_3711_);
v___x_3714_ = lean_ptr_addr(v___x_3712_);
v___x_3715_ = lean_usize_dec_eq(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3723_; 
v_isSharedCheck_3723_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3723_ == 0)
{
lean_object* v_unused_3724_; 
v_unused_3724_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3724_);
v___x_3717_ = v_code_3438_;
v_isShared_3718_ = v_isSharedCheck_3723_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v_code_3438_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3723_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3712_);
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3712_);
v___x_3720_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
return v___x_3721_;
}
}
}
else
{
lean_object* v___x_3725_; 
lean_dec_ref(v___x_3712_);
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v_code_3438_);
return v___x_3725_;
}
}
case 7:
{
lean_object* v_fvarId_3726_; lean_object* v_i_3727_; lean_object* v_y_3728_; lean_object* v_k_3729_; lean_object* v___x_3730_; 
v_fvarId_3726_ = lean_ctor_get(v_code_3438_, 0);
v_i_3727_ = lean_ctor_get(v_code_3438_, 1);
v_y_3728_ = lean_ctor_get(v_code_3438_, 2);
v_k_3729_ = lean_ctor_get(v_code_3438_, 3);
lean_inc(v_fvarId_3726_);
v___x_3730_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_3726_, v_t_3437_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_fvarId_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_fvarId_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_fvarId_3731_);
lean_dec_ref_known(v___x_3730_, 1);
lean_inc(v_y_3728_);
v___x_3732_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3436_, v_a_3439_, v_y_3728_, v_t_3437_);
lean_inc_ref(v_k_3729_);
v___x_3733_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_3729_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3807_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3807_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3807_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
size_t v___x_3738_; size_t v___x_3739_; uint8_t v___x_3740_; 
v___x_3738_ = lean_ptr_addr(v_fvarId_3726_);
v___x_3739_ = lean_ptr_addr(v_fvarId_3731_);
v___x_3740_ = lean_usize_dec_eq(v___x_3738_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3750_; 
lean_inc(v_i_3727_);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3751_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3754_);
v___x_3742_ = v_code_3438_;
v_isShared_3743_ = v_isSharedCheck_3750_;
goto v_resetjp_3741_;
}
else
{
lean_dec(v_code_3438_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3750_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 3, v_a_3734_);
lean_ctor_set(v___x_3742_, 2, v___x_3732_);
lean_ctor_set(v___x_3742_, 0, v_fvarId_3731_);
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_fvarId_3731_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_i_3727_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v_a_3734_);
v___x_3745_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3747_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3745_);
v___x_3747_ = v___x_3736_;
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
uint8_t v___x_3755_; 
v___x_3755_ = lean_nat_dec_eq(v_i_3727_, v_i_3727_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3765_; 
lean_inc(v_i_3727_);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3766_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3769_);
v___x_3757_ = v_code_3438_;
v_isShared_3758_ = v_isSharedCheck_3765_;
goto v_resetjp_3756_;
}
else
{
lean_dec(v_code_3438_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3765_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 3, v_a_3734_);
lean_ctor_set(v___x_3757_, 2, v___x_3732_);
lean_ctor_set(v___x_3757_, 0, v_fvarId_3731_);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_fvarId_3731_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_i_3727_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_a_3734_);
v___x_3760_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3760_);
v___x_3762_ = v___x_3736_;
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
v___x_3770_ = lean_ptr_addr(v_y_3728_);
v___x_3771_ = lean_ptr_addr(v___x_3732_);
v___x_3772_ = lean_usize_dec_eq(v___x_3770_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3782_; 
lean_inc(v_i_3727_);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; lean_object* v_unused_3784_; lean_object* v_unused_3785_; lean_object* v_unused_3786_; 
v_unused_3783_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3786_);
v___x_3774_ = v_code_3438_;
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v_code_3438_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 3, v_a_3734_);
lean_ctor_set(v___x_3774_, 2, v___x_3732_);
lean_ctor_set(v___x_3774_, 0, v_fvarId_3731_);
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_fvarId_3731_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_i_3727_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_a_3734_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3777_);
v___x_3779_ = v___x_3736_;
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
v___x_3787_ = lean_ptr_addr(v_k_3729_);
v___x_3788_ = lean_ptr_addr(v_a_3734_);
v___x_3789_ = lean_usize_dec_eq(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3799_; 
lean_inc(v_i_3727_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3800_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3803_);
v___x_3791_ = v_code_3438_;
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v_code_3438_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 3, v_a_3734_);
lean_ctor_set(v___x_3791_, 2, v___x_3732_);
lean_ctor_set(v___x_3791_, 0, v_fvarId_3731_);
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_fvarId_3731_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_i_3727_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_a_3734_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3794_);
v___x_3796_ = v___x_3736_;
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
lean_dec(v_a_3734_);
lean_dec(v___x_3732_);
lean_dec(v_fvarId_3731_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_code_3438_);
v___x_3805_ = v___x_3736_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_code_3438_);
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
lean_dec(v___x_3732_);
lean_dec(v_fvarId_3731_);
lean_dec_ref_known(v_code_3438_, 4);
return v___x_3733_;
}
}
else
{
lean_object* v___x_3808_; 
lean_dec_ref_known(v_code_3438_, 4);
v___x_3808_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3808_;
}
}
case 8:
{
lean_object* v_fvarId_3809_; lean_object* v_i_3810_; lean_object* v_y_3811_; lean_object* v_k_3812_; lean_object* v___x_3813_; 
v_fvarId_3809_ = lean_ctor_get(v_code_3438_, 0);
v_i_3810_ = lean_ctor_get(v_code_3438_, 1);
v_y_3811_ = lean_ctor_get(v_code_3438_, 2);
v_k_3812_ = lean_ctor_get(v_code_3438_, 3);
lean_inc(v_fvarId_3809_);
v___x_3813_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_3809_, v_t_3437_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_fvarId_3814_; lean_object* v___x_3815_; 
v_fvarId_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_fvarId_3814_);
lean_dec_ref_known(v___x_3813_, 1);
lean_inc(v_y_3811_);
v___x_3815_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_y_3811_, v_t_3437_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_fvarId_3816_; lean_object* v___x_3817_; 
v_fvarId_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_fvarId_3816_);
lean_dec_ref_known(v___x_3815_, 1);
lean_inc_ref(v_k_3812_);
v___x_3817_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_3812_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3891_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3891_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3891_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
size_t v___x_3822_; size_t v___x_3823_; uint8_t v___x_3824_; 
v___x_3822_ = lean_ptr_addr(v_fvarId_3809_);
v___x_3823_ = lean_ptr_addr(v_fvarId_3814_);
v___x_3824_ = lean_usize_dec_eq(v___x_3822_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3834_; 
lean_inc(v_i_3810_);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3835_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3838_);
v___x_3826_ = v_code_3438_;
v_isShared_3827_ = v_isSharedCheck_3834_;
goto v_resetjp_3825_;
}
else
{
lean_dec(v_code_3438_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3834_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 3, v_a_3818_);
lean_ctor_set(v___x_3826_, 2, v_fvarId_3816_);
lean_ctor_set(v___x_3826_, 0, v_fvarId_3814_);
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_fvarId_3814_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_i_3810_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_fvarId_3816_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_a_3818_);
v___x_3829_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3831_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3829_);
v___x_3831_ = v___x_3820_;
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
uint8_t v___x_3839_; 
v___x_3839_ = lean_nat_dec_eq(v_i_3810_, v_i_3810_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3849_; 
lean_inc(v_i_3810_);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3849_ == 0)
{
lean_object* v_unused_3850_; lean_object* v_unused_3851_; lean_object* v_unused_3852_; lean_object* v_unused_3853_; 
v_unused_3850_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3853_);
v___x_3841_ = v_code_3438_;
v_isShared_3842_ = v_isSharedCheck_3849_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v_code_3438_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3849_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 3, v_a_3818_);
lean_ctor_set(v___x_3841_, 2, v_fvarId_3816_);
lean_ctor_set(v___x_3841_, 0, v_fvarId_3814_);
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_fvarId_3814_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_i_3810_);
lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_fvarId_3816_);
lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_a_3818_);
v___x_3844_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3846_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3844_);
v___x_3846_ = v___x_3820_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
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
else
{
size_t v___x_3854_; size_t v___x_3855_; uint8_t v___x_3856_; 
v___x_3854_ = lean_ptr_addr(v_y_3811_);
v___x_3855_ = lean_ptr_addr(v_fvarId_3816_);
v___x_3856_ = lean_usize_dec_eq(v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3866_; 
lean_inc(v_i_3810_);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; 
v_unused_3867_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3870_);
v___x_3858_ = v_code_3438_;
v_isShared_3859_ = v_isSharedCheck_3866_;
goto v_resetjp_3857_;
}
else
{
lean_dec(v_code_3438_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3866_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 3, v_a_3818_);
lean_ctor_set(v___x_3858_, 2, v_fvarId_3816_);
lean_ctor_set(v___x_3858_, 0, v_fvarId_3814_);
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_fvarId_3814_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_i_3810_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_fvarId_3816_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_a_3818_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3861_);
v___x_3863_ = v___x_3820_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
size_t v___x_3871_; size_t v___x_3872_; uint8_t v___x_3873_; 
v___x_3871_ = lean_ptr_addr(v_k_3812_);
v___x_3872_ = lean_ptr_addr(v_a_3818_);
v___x_3873_ = lean_usize_dec_eq(v___x_3871_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3883_; 
lean_inc(v_i_3810_);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; 
v_unused_3884_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3887_);
v___x_3875_ = v_code_3438_;
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
else
{
lean_dec(v_code_3438_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 3, v_a_3818_);
lean_ctor_set(v___x_3875_, 2, v_fvarId_3816_);
lean_ctor_set(v___x_3875_, 0, v_fvarId_3814_);
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_fvarId_3814_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_i_3810_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_fvarId_3816_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_a_3818_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3880_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3878_);
v___x_3880_ = v___x_3820_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v___x_3889_; 
lean_dec(v_a_3818_);
lean_dec(v_fvarId_3816_);
lean_dec(v_fvarId_3814_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v_code_3438_);
v___x_3889_ = v___x_3820_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_code_3438_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3816_);
lean_dec(v_fvarId_3814_);
lean_dec_ref_known(v_code_3438_, 4);
return v___x_3817_;
}
}
else
{
lean_object* v___x_3892_; 
lean_dec(v_fvarId_3814_);
lean_dec_ref_known(v_code_3438_, 4);
v___x_3892_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3892_;
}
}
else
{
lean_object* v___x_3893_; 
lean_dec_ref_known(v_code_3438_, 4);
v___x_3893_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3893_;
}
}
case 9:
{
lean_object* v_fvarId_3894_; lean_object* v_i_3895_; lean_object* v_offset_3896_; lean_object* v_y_3897_; lean_object* v_ty_3898_; lean_object* v_k_3899_; lean_object* v___x_3900_; 
v_fvarId_3894_ = lean_ctor_get(v_code_3438_, 0);
v_i_3895_ = lean_ctor_get(v_code_3438_, 1);
v_offset_3896_ = lean_ctor_get(v_code_3438_, 2);
v_y_3897_ = lean_ctor_get(v_code_3438_, 3);
v_ty_3898_ = lean_ctor_get(v_code_3438_, 4);
v_k_3899_ = lean_ctor_get(v_code_3438_, 5);
lean_inc(v_fvarId_3894_);
v___x_3900_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_3894_, v_t_3437_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_fvarId_3901_; lean_object* v___x_3902_; 
v_fvarId_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_fvarId_3901_);
lean_dec_ref_known(v___x_3900_, 1);
lean_inc(v_y_3897_);
v___x_3902_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_y_3897_, v_t_3437_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_fvarId_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_fvarId_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_fvarId_3903_);
lean_dec_ref_known(v___x_3902_, 1);
lean_inc_ref(v_ty_3898_);
v___x_3904_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3436_, v_a_3439_, v_t_3437_, v_ty_3898_);
lean_inc_ref(v_k_3899_);
v___x_3905_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_3899_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_4023_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_4023_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_4023_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
size_t v___x_3910_; size_t v___x_3911_; uint8_t v___x_3912_; 
v___x_3910_ = lean_ptr_addr(v_fvarId_3894_);
v___x_3911_ = lean_ptr_addr(v_fvarId_3901_);
v___x_3912_ = lean_usize_dec_eq(v___x_3910_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3922_; 
lean_inc(v_offset_3896_);
lean_inc(v_i_3895_);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3922_ == 0)
{
lean_object* v_unused_3923_; lean_object* v_unused_3924_; lean_object* v_unused_3925_; lean_object* v_unused_3926_; lean_object* v_unused_3927_; lean_object* v_unused_3928_; 
v_unused_3923_ = lean_ctor_get(v_code_3438_, 5);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_code_3438_, 4);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3928_);
v___x_3914_ = v_code_3438_;
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
else
{
lean_dec(v_code_3438_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 5, v_a_3906_);
lean_ctor_set(v___x_3914_, 4, v___x_3904_);
lean_ctor_set(v___x_3914_, 3, v_fvarId_3903_);
lean_ctor_set(v___x_3914_, 0, v_fvarId_3901_);
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_fvarId_3901_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_i_3895_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v_offset_3896_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v_fvarId_3903_);
lean_ctor_set(v_reuseFailAlloc_3921_, 4, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3921_, 5, v_a_3906_);
v___x_3917_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3919_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3917_);
v___x_3919_ = v___x_3908_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
uint8_t v___x_3929_; 
v___x_3929_ = lean_nat_dec_eq(v_i_3895_, v_i_3895_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3939_; 
lean_inc(v_offset_3896_);
lean_inc(v_i_3895_);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; 
v_unused_3940_ = lean_ctor_get(v_code_3438_, 5);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_code_3438_, 4);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3945_);
v___x_3931_ = v_code_3438_;
v_isShared_3932_ = v_isSharedCheck_3939_;
goto v_resetjp_3930_;
}
else
{
lean_dec(v_code_3438_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3939_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 5, v_a_3906_);
lean_ctor_set(v___x_3931_, 4, v___x_3904_);
lean_ctor_set(v___x_3931_, 3, v_fvarId_3903_);
lean_ctor_set(v___x_3931_, 0, v_fvarId_3901_);
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_fvarId_3901_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_i_3895_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_offset_3896_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_fvarId_3903_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3938_, 5, v_a_3906_);
v___x_3934_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3936_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3934_);
v___x_3936_ = v___x_3908_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_eq(v_offset_3896_, v_offset_3896_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3956_; 
lean_inc(v_offset_3896_);
lean_inc(v_i_3895_);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3956_ == 0)
{
lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; lean_object* v_unused_3961_; lean_object* v_unused_3962_; 
v_unused_3957_ = lean_ctor_get(v_code_3438_, 5);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_code_3438_, 4);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3962_);
v___x_3948_ = v_code_3438_;
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v_code_3438_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 5, v_a_3906_);
lean_ctor_set(v___x_3948_, 4, v___x_3904_);
lean_ctor_set(v___x_3948_, 3, v_fvarId_3903_);
lean_ctor_set(v___x_3948_, 0, v_fvarId_3901_);
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_fvarId_3901_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_i_3895_);
lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_offset_3896_);
lean_ctor_set(v_reuseFailAlloc_3955_, 3, v_fvarId_3903_);
lean_ctor_set(v_reuseFailAlloc_3955_, 4, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3955_, 5, v_a_3906_);
v___x_3951_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3953_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3951_);
v___x_3953_ = v___x_3908_;
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
v___x_3963_ = lean_ptr_addr(v_y_3897_);
v___x_3964_ = lean_ptr_addr(v_fvarId_3903_);
v___x_3965_ = lean_usize_dec_eq(v___x_3963_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3975_; 
lean_inc(v_offset_3896_);
lean_inc(v_i_3895_);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; lean_object* v_unused_3977_; lean_object* v_unused_3978_; lean_object* v_unused_3979_; lean_object* v_unused_3980_; lean_object* v_unused_3981_; 
v_unused_3976_ = lean_ctor_get(v_code_3438_, 5);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_code_3438_, 4);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_3981_);
v___x_3967_ = v_code_3438_;
v_isShared_3968_ = v_isSharedCheck_3975_;
goto v_resetjp_3966_;
}
else
{
lean_dec(v_code_3438_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3975_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 5, v_a_3906_);
lean_ctor_set(v___x_3967_, 4, v___x_3904_);
lean_ctor_set(v___x_3967_, 3, v_fvarId_3903_);
lean_ctor_set(v___x_3967_, 0, v_fvarId_3901_);
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_fvarId_3901_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_i_3895_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_offset_3896_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_fvarId_3903_);
lean_ctor_set(v_reuseFailAlloc_3974_, 4, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3974_, 5, v_a_3906_);
v___x_3970_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3972_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3970_);
v___x_3972_ = v___x_3908_;
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
size_t v___x_3982_; size_t v___x_3983_; uint8_t v___x_3984_; 
v___x_3982_ = lean_ptr_addr(v_ty_3898_);
v___x_3983_ = lean_ptr_addr(v___x_3904_);
v___x_3984_ = lean_usize_dec_eq(v___x_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3994_; 
lean_inc(v_offset_3896_);
lean_inc(v_i_3895_);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; lean_object* v_unused_3996_; lean_object* v_unused_3997_; lean_object* v_unused_3998_; lean_object* v_unused_3999_; lean_object* v_unused_4000_; 
v_unused_3995_ = lean_ctor_get(v_code_3438_, 5);
lean_dec(v_unused_3995_);
v_unused_3996_ = lean_ctor_get(v_code_3438_, 4);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_3997_);
v_unused_3998_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_3998_);
v_unused_3999_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4000_);
v___x_3986_ = v_code_3438_;
v_isShared_3987_ = v_isSharedCheck_3994_;
goto v_resetjp_3985_;
}
else
{
lean_dec(v_code_3438_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3994_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 5, v_a_3906_);
lean_ctor_set(v___x_3986_, 4, v___x_3904_);
lean_ctor_set(v___x_3986_, 3, v_fvarId_3903_);
lean_ctor_set(v___x_3986_, 0, v_fvarId_3901_);
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fvarId_3901_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_i_3895_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_offset_3896_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_fvarId_3903_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3993_, 5, v_a_3906_);
v___x_3989_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3991_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3989_);
v___x_3991_ = v___x_3908_;
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
size_t v___x_4001_; size_t v___x_4002_; uint8_t v___x_4003_; 
v___x_4001_ = lean_ptr_addr(v_k_3899_);
v___x_4002_ = lean_ptr_addr(v_a_3906_);
v___x_4003_ = lean_usize_dec_eq(v___x_4001_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4013_; 
lean_inc(v_offset_3896_);
lean_inc(v_i_3895_);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; lean_object* v_unused_4017_; lean_object* v_unused_4018_; lean_object* v_unused_4019_; 
v_unused_4014_ = lean_ctor_get(v_code_3438_, 5);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_code_3438_, 4);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_4016_);
v_unused_4017_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4017_);
v_unused_4018_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4018_);
v_unused_4019_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4019_);
v___x_4005_ = v_code_3438_;
v_isShared_4006_ = v_isSharedCheck_4013_;
goto v_resetjp_4004_;
}
else
{
lean_dec(v_code_3438_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4013_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 5, v_a_3906_);
lean_ctor_set(v___x_4005_, 4, v___x_3904_);
lean_ctor_set(v___x_4005_, 3, v_fvarId_3903_);
lean_ctor_set(v___x_4005_, 0, v_fvarId_3901_);
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_fvarId_3901_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_i_3895_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_offset_3896_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_fvarId_3903_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_4012_, 5, v_a_3906_);
v___x_4008_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4010_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_4008_);
v___x_4010_ = v___x_3908_;
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
lean_object* v___x_4021_; 
lean_dec(v_a_3906_);
lean_dec_ref(v___x_3904_);
lean_dec(v_fvarId_3903_);
lean_dec(v_fvarId_3901_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v_code_3438_);
v___x_4021_ = v___x_3908_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_code_3438_);
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
}
}
}
}
}
else
{
lean_dec_ref(v___x_3904_);
lean_dec(v_fvarId_3903_);
lean_dec(v_fvarId_3901_);
lean_dec_ref_known(v_code_3438_, 6);
return v___x_3905_;
}
}
else
{
lean_object* v___x_4024_; 
lean_dec(v_fvarId_3901_);
lean_dec_ref_known(v_code_3438_, 6);
v___x_4024_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_4024_;
}
}
else
{
lean_object* v___x_4025_; 
lean_dec_ref_known(v_code_3438_, 6);
v___x_4025_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_4025_;
}
}
case 10:
{
lean_object* v_fvarId_4026_; lean_object* v_cidx_4027_; lean_object* v_k_4028_; lean_object* v___x_4029_; 
v_fvarId_4026_ = lean_ctor_get(v_code_3438_, 0);
v_cidx_4027_ = lean_ctor_get(v_code_3438_, 1);
v_k_4028_ = lean_ctor_get(v_code_3438_, 2);
lean_inc(v_fvarId_4026_);
v___x_4029_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_4026_, v_t_3437_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_fvarId_4030_; lean_object* v___x_4031_; 
v_fvarId_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_fvarId_4030_);
lean_dec_ref_known(v___x_4029_, 1);
lean_inc_ref(v_k_4028_);
v___x_4031_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_4028_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4085_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4085_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4085_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
size_t v___x_4036_; size_t v___x_4037_; uint8_t v___x_4038_; 
v___x_4036_ = lean_ptr_addr(v_fvarId_4026_);
v___x_4037_ = lean_ptr_addr(v_fvarId_4030_);
v___x_4038_ = lean_usize_dec_eq(v___x_4036_, v___x_4037_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4048_; 
lean_inc(v_cidx_4027_);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4048_ == 0)
{
lean_object* v_unused_4049_; lean_object* v_unused_4050_; lean_object* v_unused_4051_; 
v_unused_4049_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4049_);
v_unused_4050_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4050_);
v_unused_4051_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4051_);
v___x_4040_ = v_code_3438_;
v_isShared_4041_ = v_isSharedCheck_4048_;
goto v_resetjp_4039_;
}
else
{
lean_dec(v_code_3438_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4048_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 2, v_a_4032_);
lean_ctor_set(v___x_4040_, 0, v_fvarId_4030_);
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_fvarId_4030_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v_cidx_4027_);
lean_ctor_set(v_reuseFailAlloc_4047_, 2, v_a_4032_);
v___x_4043_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4045_; 
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v___x_4043_);
v___x_4045_ = v___x_4034_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
else
{
uint8_t v___x_4052_; 
v___x_4052_ = lean_nat_dec_eq(v_cidx_4027_, v_cidx_4027_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4062_; 
lean_inc(v_cidx_4027_);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; lean_object* v_unused_4064_; lean_object* v_unused_4065_; 
v_unused_4063_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4065_);
v___x_4054_ = v_code_3438_;
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
else
{
lean_dec(v_code_3438_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 2, v_a_4032_);
lean_ctor_set(v___x_4054_, 0, v_fvarId_4030_);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_fvarId_4030_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_cidx_4027_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_a_4032_);
v___x_4057_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v___x_4057_);
v___x_4059_ = v___x_4034_;
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
size_t v___x_4066_; size_t v___x_4067_; uint8_t v___x_4068_; 
v___x_4066_ = lean_ptr_addr(v_k_4028_);
v___x_4067_ = lean_ptr_addr(v_a_4032_);
v___x_4068_ = lean_usize_dec_eq(v___x_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4078_; 
lean_inc(v_cidx_4027_);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; lean_object* v_unused_4080_; lean_object* v_unused_4081_; 
v_unused_4079_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4079_);
v_unused_4080_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4080_);
v_unused_4081_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4081_);
v___x_4070_ = v_code_3438_;
v_isShared_4071_ = v_isSharedCheck_4078_;
goto v_resetjp_4069_;
}
else
{
lean_dec(v_code_3438_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4078_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 2, v_a_4032_);
lean_ctor_set(v___x_4070_, 0, v_fvarId_4030_);
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_fvarId_4030_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_cidx_4027_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_a_4032_);
v___x_4073_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4075_; 
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v___x_4073_);
v___x_4075_ = v___x_4034_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_object* v___x_4083_; 
lean_dec(v_a_4032_);
lean_dec(v_fvarId_4030_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v_code_3438_);
v___x_4083_ = v___x_4034_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_code_3438_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4030_);
lean_dec_ref_known(v_code_3438_, 3);
return v___x_4031_;
}
}
else
{
lean_object* v___x_4086_; 
lean_dec_ref_known(v_code_3438_, 3);
v___x_4086_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_4086_;
}
}
case 11:
{
lean_object* v_fvarId_4087_; lean_object* v_n_4088_; uint8_t v_check_4089_; uint8_t v_persistent_4090_; lean_object* v_k_4091_; lean_object* v___x_4092_; 
v_fvarId_4087_ = lean_ctor_get(v_code_3438_, 0);
v_n_4088_ = lean_ctor_get(v_code_3438_, 1);
v_check_4089_ = lean_ctor_get_uint8(v_code_3438_, sizeof(void*)*3);
v_persistent_4090_ = lean_ctor_get_uint8(v_code_3438_, sizeof(void*)*3 + 1);
v_k_4091_ = lean_ctor_get(v_code_3438_, 2);
lean_inc(v_fvarId_4087_);
v___x_4092_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_4087_, v_t_3437_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_fvarId_4093_; lean_object* v___x_4094_; 
v_fvarId_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_fvarId_4093_);
lean_dec_ref_known(v___x_4092_, 1);
lean_inc_ref(v_k_4091_);
v___x_4094_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_4091_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4148_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4097_ = v___x_4094_;
v_isShared_4098_ = v_isSharedCheck_4148_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4148_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
size_t v___x_4099_; size_t v___x_4100_; uint8_t v___x_4101_; 
v___x_4099_ = lean_ptr_addr(v_fvarId_4087_);
v___x_4100_ = lean_ptr_addr(v_fvarId_4093_);
v___x_4101_ = lean_usize_dec_eq(v___x_4099_, v___x_4100_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4111_; 
lean_inc(v_n_4088_);
v_isSharedCheck_4111_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4111_ == 0)
{
lean_object* v_unused_4112_; lean_object* v_unused_4113_; lean_object* v_unused_4114_; 
v_unused_4112_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4112_);
v_unused_4113_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4113_);
v_unused_4114_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4114_);
v___x_4103_ = v_code_3438_;
v_isShared_4104_ = v_isSharedCheck_4111_;
goto v_resetjp_4102_;
}
else
{
lean_dec(v_code_3438_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4111_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 2, v_a_4095_);
lean_ctor_set(v___x_4103_, 0, v_fvarId_4093_);
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_fvarId_4093_);
lean_ctor_set(v_reuseFailAlloc_4110_, 1, v_n_4088_);
lean_ctor_set(v_reuseFailAlloc_4110_, 2, v_a_4095_);
lean_ctor_set_uint8(v_reuseFailAlloc_4110_, sizeof(void*)*3, v_check_4089_);
lean_ctor_set_uint8(v_reuseFailAlloc_4110_, sizeof(void*)*3 + 1, v_persistent_4090_);
v___x_4106_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4108_; 
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4106_);
v___x_4108_ = v___x_4097_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
uint8_t v___x_4115_; 
v___x_4115_ = lean_nat_dec_eq(v_n_4088_, v_n_4088_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4125_; 
lean_inc(v_n_4088_);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; lean_object* v_unused_4127_; lean_object* v_unused_4128_; 
v_unused_4126_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4126_);
v_unused_4127_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4128_);
v___x_4117_ = v_code_3438_;
v_isShared_4118_ = v_isSharedCheck_4125_;
goto v_resetjp_4116_;
}
else
{
lean_dec(v_code_3438_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4125_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 2, v_a_4095_);
lean_ctor_set(v___x_4117_, 0, v_fvarId_4093_);
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_fvarId_4093_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v_n_4088_);
lean_ctor_set(v_reuseFailAlloc_4124_, 2, v_a_4095_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*3, v_check_4089_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*3 + 1, v_persistent_4090_);
v___x_4120_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4122_; 
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4120_);
v___x_4122_ = v___x_4097_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
size_t v___x_4129_; size_t v___x_4130_; uint8_t v___x_4131_; 
v___x_4129_ = lean_ptr_addr(v_k_4091_);
v___x_4130_ = lean_ptr_addr(v_a_4095_);
v___x_4131_ = lean_usize_dec_eq(v___x_4129_, v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4141_; 
lean_inc(v_n_4088_);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; lean_object* v_unused_4143_; lean_object* v_unused_4144_; 
v_unused_4142_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4143_);
v_unused_4144_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4144_);
v___x_4133_ = v_code_3438_;
v_isShared_4134_ = v_isSharedCheck_4141_;
goto v_resetjp_4132_;
}
else
{
lean_dec(v_code_3438_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4141_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 2, v_a_4095_);
lean_ctor_set(v___x_4133_, 0, v_fvarId_4093_);
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_fvarId_4093_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_n_4088_);
lean_ctor_set(v_reuseFailAlloc_4140_, 2, v_a_4095_);
lean_ctor_set_uint8(v_reuseFailAlloc_4140_, sizeof(void*)*3, v_check_4089_);
lean_ctor_set_uint8(v_reuseFailAlloc_4140_, sizeof(void*)*3 + 1, v_persistent_4090_);
v___x_4136_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4138_; 
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4136_);
v___x_4138_ = v___x_4097_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
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
else
{
lean_object* v___x_4146_; 
lean_dec(v_a_4095_);
lean_dec(v_fvarId_4093_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v_code_3438_);
v___x_4146_ = v___x_4097_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_code_3438_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4093_);
lean_dec_ref_known(v_code_3438_, 3);
return v___x_4094_;
}
}
else
{
lean_object* v___x_4149_; 
lean_dec_ref_known(v_code_3438_, 3);
v___x_4149_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_4149_;
}
}
case 12:
{
lean_object* v_fvarId_4150_; lean_object* v_n_4151_; uint8_t v_check_4152_; uint8_t v_persistent_4153_; lean_object* v_objs_x3f_4154_; lean_object* v_k_4155_; lean_object* v___x_4156_; 
v_fvarId_4150_ = lean_ctor_get(v_code_3438_, 0);
v_n_4151_ = lean_ctor_get(v_code_3438_, 1);
v_check_4152_ = lean_ctor_get_uint8(v_code_3438_, sizeof(void*)*4);
v_persistent_4153_ = lean_ctor_get_uint8(v_code_3438_, sizeof(void*)*4 + 1);
v_objs_x3f_4154_ = lean_ctor_get(v_code_3438_, 2);
v_k_4155_ = lean_ctor_get(v_code_3438_, 3);
lean_inc(v_fvarId_4150_);
v___x_4156_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_4150_, v_t_3437_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_fvarId_4157_; lean_object* v___x_4158_; 
v_fvarId_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_fvarId_4157_);
lean_dec_ref_known(v___x_4156_, 1);
lean_inc_ref(v_k_4155_);
v___x_4158_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_4155_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4231_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4231_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4231_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
size_t v___x_4163_; size_t v___x_4164_; uint8_t v___x_4165_; 
v___x_4163_ = lean_ptr_addr(v_fvarId_4150_);
v___x_4164_ = lean_ptr_addr(v_fvarId_4157_);
v___x_4165_ = lean_usize_dec_eq(v___x_4163_, v___x_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4175_; 
lean_inc(v_objs_x3f_4154_);
lean_inc(v_n_4151_);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; lean_object* v_unused_4177_; lean_object* v_unused_4178_; lean_object* v_unused_4179_; 
v_unused_4176_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_4176_);
v_unused_4177_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4179_);
v___x_4167_ = v_code_3438_;
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_code_3438_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 3, v_a_4159_);
lean_ctor_set(v___x_4167_, 0, v_fvarId_4157_);
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_fvarId_4157_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v_n_4151_);
lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_objs_x3f_4154_);
lean_ctor_set(v_reuseFailAlloc_4174_, 3, v_a_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4174_, sizeof(void*)*4, v_check_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4174_, sizeof(void*)*4 + 1, v_persistent_4153_);
v___x_4170_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4172_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4170_);
v___x_4172_ = v___x_4161_;
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
uint8_t v___x_4180_; 
v___x_4180_ = lean_nat_dec_eq(v_n_4151_, v_n_4151_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4190_; 
lean_inc(v_objs_x3f_4154_);
lean_inc(v_n_4151_);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; lean_object* v_unused_4192_; lean_object* v_unused_4193_; lean_object* v_unused_4194_; 
v_unused_4191_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_4191_);
v_unused_4192_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4193_);
v_unused_4194_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4194_);
v___x_4182_ = v_code_3438_;
v_isShared_4183_ = v_isSharedCheck_4190_;
goto v_resetjp_4181_;
}
else
{
lean_dec(v_code_3438_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4190_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 3, v_a_4159_);
lean_ctor_set(v___x_4182_, 0, v_fvarId_4157_);
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_fvarId_4157_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_n_4151_);
lean_ctor_set(v_reuseFailAlloc_4189_, 2, v_objs_x3f_4154_);
lean_ctor_set(v_reuseFailAlloc_4189_, 3, v_a_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4189_, sizeof(void*)*4, v_check_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4189_, sizeof(void*)*4 + 1, v_persistent_4153_);
v___x_4185_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4187_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4185_);
v___x_4187_ = v___x_4161_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
size_t v___x_4195_; uint8_t v___x_4196_; 
v___x_4195_ = lean_ptr_addr(v_objs_x3f_4154_);
v___x_4196_ = lean_usize_dec_eq(v___x_4195_, v___x_4195_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4206_; 
lean_inc(v_objs_x3f_4154_);
lean_inc(v_n_4151_);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; lean_object* v_unused_4208_; lean_object* v_unused_4209_; lean_object* v_unused_4210_; 
v_unused_4207_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_4207_);
v_unused_4208_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4208_);
v_unused_4209_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4209_);
v_unused_4210_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4210_);
v___x_4198_ = v_code_3438_;
v_isShared_4199_ = v_isSharedCheck_4206_;
goto v_resetjp_4197_;
}
else
{
lean_dec(v_code_3438_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4206_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 3, v_a_4159_);
lean_ctor_set(v___x_4198_, 0, v_fvarId_4157_);
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_fvarId_4157_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_n_4151_);
lean_ctor_set(v_reuseFailAlloc_4205_, 2, v_objs_x3f_4154_);
lean_ctor_set(v_reuseFailAlloc_4205_, 3, v_a_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4205_, sizeof(void*)*4, v_check_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4205_, sizeof(void*)*4 + 1, v_persistent_4153_);
v___x_4201_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4203_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4201_);
v___x_4203_ = v___x_4161_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
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
size_t v___x_4211_; size_t v___x_4212_; uint8_t v___x_4213_; 
v___x_4211_ = lean_ptr_addr(v_k_4155_);
v___x_4212_ = lean_ptr_addr(v_a_4159_);
v___x_4213_ = lean_usize_dec_eq(v___x_4211_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4223_; 
lean_inc(v_objs_x3f_4154_);
lean_inc(v_n_4151_);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; lean_object* v_unused_4225_; lean_object* v_unused_4226_; lean_object* v_unused_4227_; 
v_unused_4224_ = lean_ctor_get(v_code_3438_, 3);
lean_dec(v_unused_4224_);
v_unused_4225_ = lean_ctor_get(v_code_3438_, 2);
lean_dec(v_unused_4225_);
v_unused_4226_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4226_);
v_unused_4227_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4227_);
v___x_4215_ = v_code_3438_;
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
else
{
lean_dec(v_code_3438_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 3, v_a_4159_);
lean_ctor_set(v___x_4215_, 0, v_fvarId_4157_);
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_fvarId_4157_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_n_4151_);
lean_ctor_set(v_reuseFailAlloc_4222_, 2, v_objs_x3f_4154_);
lean_ctor_set(v_reuseFailAlloc_4222_, 3, v_a_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4222_, sizeof(void*)*4, v_check_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4222_, sizeof(void*)*4 + 1, v_persistent_4153_);
v___x_4218_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
lean_object* v___x_4220_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4218_);
v___x_4220_ = v___x_4161_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
else
{
lean_object* v___x_4229_; 
lean_dec(v_a_4159_);
lean_dec(v_fvarId_4157_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v_code_3438_);
v___x_4229_ = v___x_4161_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_code_3438_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4157_);
lean_dec_ref_known(v_code_3438_, 4);
return v___x_4158_;
}
}
else
{
lean_object* v___x_4232_; 
lean_dec_ref_known(v_code_3438_, 4);
v___x_4232_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_4232_;
}
}
default: 
{
lean_object* v_fvarId_4233_; lean_object* v_k_4234_; lean_object* v___x_4235_; 
v_fvarId_4233_ = lean_ctor_get(v_code_3438_, 0);
v_k_4234_ = lean_ctor_get(v_code_3438_, 1);
lean_inc(v_fvarId_4233_);
v___x_4235_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3439_, v_fvarId_4233_, v_t_3437_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_fvarId_4236_; lean_object* v___x_4237_; 
v_fvarId_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_fvarId_4236_);
lean_dec_ref_known(v___x_4235_, 1);
lean_inc_ref(v_k_4234_);
v___x_4237_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3436_, v_t_3437_, v_k_4234_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4275_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4275_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4275_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
size_t v___x_4242_; size_t v___x_4243_; uint8_t v___x_4244_; 
v___x_4242_ = lean_ptr_addr(v_fvarId_4233_);
v___x_4243_ = lean_ptr_addr(v_fvarId_4236_);
v___x_4244_ = lean_usize_dec_eq(v___x_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4254_; 
v_isSharedCheck_4254_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4254_ == 0)
{
lean_object* v_unused_4255_; lean_object* v_unused_4256_; 
v_unused_4255_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4255_);
v_unused_4256_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4256_);
v___x_4246_ = v_code_3438_;
v_isShared_4247_ = v_isSharedCheck_4254_;
goto v_resetjp_4245_;
}
else
{
lean_dec(v_code_3438_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4254_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 1, v_a_4238_);
lean_ctor_set(v___x_4246_, 0, v_fvarId_4236_);
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_fvarId_4236_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_a_4238_);
v___x_4249_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4251_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4249_);
v___x_4251_ = v___x_4240_;
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
size_t v___x_4257_; size_t v___x_4258_; uint8_t v___x_4259_; 
v___x_4257_ = lean_ptr_addr(v_k_4234_);
v___x_4258_ = lean_ptr_addr(v_a_4238_);
v___x_4259_ = lean_usize_dec_eq(v___x_4257_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4269_; 
v_isSharedCheck_4269_ = !lean_is_exclusive(v_code_3438_);
if (v_isSharedCheck_4269_ == 0)
{
lean_object* v_unused_4270_; lean_object* v_unused_4271_; 
v_unused_4270_ = lean_ctor_get(v_code_3438_, 1);
lean_dec(v_unused_4270_);
v_unused_4271_ = lean_ctor_get(v_code_3438_, 0);
lean_dec(v_unused_4271_);
v___x_4261_ = v_code_3438_;
v_isShared_4262_ = v_isSharedCheck_4269_;
goto v_resetjp_4260_;
}
else
{
lean_dec(v_code_3438_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4269_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 1, v_a_4238_);
lean_ctor_set(v___x_4261_, 0, v_fvarId_4236_);
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_fvarId_4236_);
lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_a_4238_);
v___x_4264_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
lean_object* v___x_4266_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4264_);
v___x_4266_ = v___x_4240_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
lean_object* v___x_4273_; 
lean_dec(v_a_4238_);
lean_dec(v_fvarId_4236_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v_code_3438_);
v___x_4273_ = v___x_4240_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_code_3438_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4236_);
lean_dec_ref_known(v_code_3438_, 2);
return v___x_4237_;
}
}
else
{
lean_object* v___x_4276_; 
lean_dec_ref_known(v_code_3438_, 2);
v___x_4276_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3436_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_4276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4277_, uint8_t v_t_4278_, lean_object* v_decl_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_params_4286_; lean_object* v_type_4287_; lean_object* v_value_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v_params_4286_ = lean_ctor_get(v_decl_4279_, 2);
v_type_4287_ = lean_ctor_get(v_decl_4279_, 3);
v_value_4288_ = lean_ctor_get(v_decl_4279_, 4);
lean_inc_ref(v_type_4287_);
v___x_4289_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4277_, v_a_4280_, v_t_4278_, v_type_4287_);
lean_inc_ref(v_params_4286_);
v___x_4290_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4277_, v_t_4278_, v_params_4286_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4292_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
lean_inc_ref(v_value_4288_);
v___x_4292_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4277_, v_t_4278_, v_value_4288_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4294_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref_known(v___x_4292_, 1);
v___x_4294_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4277_, v_decl_4279_, v___x_4289_, v_a_4291_, v_a_4293_, v_a_4282_);
return v___x_4294_;
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec(v_a_4291_);
lean_dec_ref(v___x_4289_);
lean_dec_ref(v_decl_4279_);
v_a_4295_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4292_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4292_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec_ref(v___x_4289_);
lean_dec_ref(v_decl_4279_);
v_a_4303_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4290_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4290_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4311_, lean_object* v_t_4312_, lean_object* v_decl_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
uint8_t v_pu_boxed_4320_; uint8_t v_t_boxed_4321_; lean_object* v_res_4322_; 
v_pu_boxed_4320_ = lean_unbox(v_pu_4311_);
v_t_boxed_4321_ = lean_unbox(v_t_4312_);
v_res_4322_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4320_, v_t_boxed_4321_, v_decl_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec_ref(v_a_4314_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4323_, lean_object* v_t_4324_, lean_object* v_i_4325_, lean_object* v_as_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
uint8_t v_pu_boxed_4333_; uint8_t v_t_boxed_4334_; lean_object* v_res_4335_; 
v_pu_boxed_4333_ = lean_unbox(v_pu_4323_);
v_t_boxed_4334_ = lean_unbox(v_t_4324_);
v_res_4335_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4333_, v_t_boxed_4334_, v_i_4325_, v_as_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec_ref(v___y_4327_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4336_, lean_object* v_t_4337_, lean_object* v_code_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_){
_start:
{
uint8_t v_pu_boxed_4345_; uint8_t v_t_boxed_4346_; lean_object* v_res_4347_; 
v_pu_boxed_4345_ = lean_unbox(v_pu_4336_);
v_t_boxed_4346_ = lean_unbox(v_t_4337_);
v_res_4347_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4345_, v_t_boxed_4346_, v_code_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
lean_dec(v_a_4341_);
lean_dec_ref(v_a_4340_);
lean_dec_ref(v_a_4339_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4348_, uint8_t v_t_4349_, uint8_t v_pu_4350_, uint8_t v_t_4351_, lean_object* v_decl_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4350_, v_t_4351_, v_decl_4352_, v___y_4353_, v___y_4355_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4360_, lean_object* v_t_4361_, lean_object* v_pu_4362_, lean_object* v_t_4363_, lean_object* v_decl_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
uint8_t v_pu_boxed_4371_; uint8_t v_t_boxed_4372_; uint8_t v_pu_boxed_4373_; uint8_t v_t_boxed_4374_; lean_object* v_res_4375_; 
v_pu_boxed_4371_ = lean_unbox(v_pu_4360_);
v_t_boxed_4372_ = lean_unbox(v_t_4361_);
v_pu_boxed_4373_ = lean_unbox(v_pu_4362_);
v_t_boxed_4374_ = lean_unbox(v_t_4363_);
v_res_4375_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4371_, v_t_boxed_4372_, v_pu_boxed_4373_, v_t_boxed_4374_, v_decl_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4376_, uint8_t v_t_4377_, uint8_t v_pu_4378_, uint8_t v_t_4379_, lean_object* v_args_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4378_, v_t_4379_, v_args_4380_, v___y_4381_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4388_, lean_object* v_t_4389_, lean_object* v_pu_4390_, lean_object* v_t_4391_, lean_object* v_args_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v_pu_boxed_4399_; uint8_t v_t_boxed_4400_; uint8_t v_pu_boxed_4401_; uint8_t v_t_boxed_4402_; lean_object* v_res_4403_; 
v_pu_boxed_4399_ = lean_unbox(v_pu_4388_);
v_t_boxed_4400_ = lean_unbox(v_t_4389_);
v_pu_boxed_4401_ = lean_unbox(v_pu_4390_);
v_t_boxed_4402_ = lean_unbox(v_t_4391_);
v_res_4403_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4399_, v_t_boxed_4400_, v_pu_boxed_4401_, v_t_boxed_4402_, v_args_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec_ref(v___y_4393_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4404_, uint8_t v_t_4405_, uint8_t v_pu_4406_, uint8_t v_t_4407_, lean_object* v_ps_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4406_, v_t_4407_, v_ps_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4416_, lean_object* v_t_4417_, lean_object* v_pu_4418_, lean_object* v_t_4419_, lean_object* v_ps_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
uint8_t v_pu_boxed_4427_; uint8_t v_t_boxed_4428_; uint8_t v_pu_boxed_4429_; uint8_t v_t_boxed_4430_; lean_object* v_res_4431_; 
v_pu_boxed_4427_ = lean_unbox(v_pu_4416_);
v_t_boxed_4428_ = lean_unbox(v_t_4417_);
v_pu_boxed_4429_ = lean_unbox(v_pu_4418_);
v_t_boxed_4430_ = lean_unbox(v_t_4419_);
v_res_4431_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4427_, v_t_boxed_4428_, v_pu_boxed_4429_, v_t_boxed_4430_, v_ps_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4432_, uint8_t v_t_4433_, lean_object* v_i_4434_, lean_object* v_as_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v___x_4442_; 
v___x_4442_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4432_, v_t_4433_, v_i_4434_, v_as_4435_, v___y_4436_, v___y_4438_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4443_, lean_object* v_t_4444_, lean_object* v_i_4445_, lean_object* v_as_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
uint8_t v_pu_boxed_4453_; uint8_t v_t_boxed_4454_; lean_object* v_res_4455_; 
v_pu_boxed_4453_ = lean_unbox(v_pu_4443_);
v_t_boxed_4454_ = lean_unbox(v_t_4444_);
v_res_4455_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4453_, v_t_boxed_4454_, v_i_4445_, v_as_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec_ref(v___y_4447_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4456_, uint8_t v_t_4457_, lean_object* v_decl_4458_, lean_object* v_inst_4459_, lean_object* v_____do__lift_4460_){
_start:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4461_ = lean_box(v_pu_4456_);
v___x_4462_ = lean_box(v_t_4457_);
v___x_4463_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4463_, 0, v___x_4461_);
lean_closure_set(v___x_4463_, 1, v___x_4462_);
lean_closure_set(v___x_4463_, 2, v_decl_4458_);
lean_closure_set(v___x_4463_, 3, v_____do__lift_4460_);
v___x_4464_ = lean_apply_2(v_inst_4459_, lean_box(0), v___x_4463_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4465_, lean_object* v_t_4466_, lean_object* v_decl_4467_, lean_object* v_inst_4468_, lean_object* v_____do__lift_4469_){
_start:
{
uint8_t v_pu_boxed_4470_; uint8_t v_t_boxed_4471_; lean_object* v_res_4472_; 
v_pu_boxed_4470_ = lean_unbox(v_pu_4465_);
v_t_boxed_4471_ = lean_unbox(v_t_4466_);
v_res_4472_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4470_, v_t_boxed_4471_, v_decl_4467_, v_inst_4468_, v_____do__lift_4469_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4473_, uint8_t v_t_4474_, lean_object* v_inst_4475_, lean_object* v_inst_4476_, lean_object* v_inst_4477_, lean_object* v_decl_4478_){
_start:
{
lean_object* v_toBind_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___f_4482_; lean_object* v___x_4483_; 
v_toBind_4479_ = lean_ctor_get(v_inst_4476_, 1);
lean_inc(v_toBind_4479_);
lean_dec_ref(v_inst_4476_);
v___x_4480_ = lean_box(v_pu_4473_);
v___x_4481_ = lean_box(v_t_4474_);
v___f_4482_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4482_, 0, v___x_4480_);
lean_closure_set(v___f_4482_, 1, v___x_4481_);
lean_closure_set(v___f_4482_, 2, v_decl_4478_);
lean_closure_set(v___f_4482_, 3, v_inst_4475_);
v___x_4483_ = lean_apply_4(v_toBind_4479_, lean_box(0), lean_box(0), v_inst_4477_, v___f_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4484_, lean_object* v_t_4485_, lean_object* v_inst_4486_, lean_object* v_inst_4487_, lean_object* v_inst_4488_, lean_object* v_decl_4489_){
_start:
{
uint8_t v_pu_boxed_4490_; uint8_t v_t_boxed_4491_; lean_object* v_res_4492_; 
v_pu_boxed_4490_ = lean_unbox(v_pu_4484_);
v_t_boxed_4491_ = lean_unbox(v_t_4485_);
v_res_4492_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4490_, v_t_boxed_4491_, v_inst_4486_, v_inst_4487_, v_inst_4488_, v_decl_4489_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4493_, uint8_t v_pu_4494_, uint8_t v_t_4495_, lean_object* v_inst_4496_, lean_object* v_inst_4497_, lean_object* v_inst_4498_, lean_object* v_decl_4499_){
_start:
{
lean_object* v_toBind_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___f_4503_; lean_object* v___x_4504_; 
v_toBind_4500_ = lean_ctor_get(v_inst_4497_, 1);
lean_inc(v_toBind_4500_);
lean_dec_ref(v_inst_4497_);
v___x_4501_ = lean_box(v_pu_4494_);
v___x_4502_ = lean_box(v_t_4495_);
v___f_4503_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4503_, 0, v___x_4501_);
lean_closure_set(v___f_4503_, 1, v___x_4502_);
lean_closure_set(v___f_4503_, 2, v_decl_4499_);
lean_closure_set(v___f_4503_, 3, v_inst_4496_);
v___x_4504_ = lean_apply_4(v_toBind_4500_, lean_box(0), lean_box(0), v_inst_4498_, v___f_4503_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4505_, lean_object* v_pu_4506_, lean_object* v_t_4507_, lean_object* v_inst_4508_, lean_object* v_inst_4509_, lean_object* v_inst_4510_, lean_object* v_decl_4511_){
_start:
{
uint8_t v_pu_boxed_4512_; uint8_t v_t_boxed_4513_; lean_object* v_res_4514_; 
v_pu_boxed_4512_ = lean_unbox(v_pu_4506_);
v_t_boxed_4513_ = lean_unbox(v_t_4507_);
v_res_4514_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4505_, v_pu_boxed_4512_, v_t_boxed_4513_, v_inst_4508_, v_inst_4509_, v_inst_4510_, v_decl_4511_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4515_, uint8_t v_t_4516_, lean_object* v_code_4517_, lean_object* v_inst_4518_, lean_object* v_____do__lift_4519_){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4520_ = lean_box(v_pu_4515_);
v___x_4521_ = lean_box(v_t_4516_);
v___x_4522_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4522_, 0, v___x_4520_);
lean_closure_set(v___x_4522_, 1, v___x_4521_);
lean_closure_set(v___x_4522_, 2, v_code_4517_);
lean_closure_set(v___x_4522_, 3, v_____do__lift_4519_);
v___x_4523_ = lean_apply_2(v_inst_4518_, lean_box(0), v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4524_, lean_object* v_t_4525_, lean_object* v_code_4526_, lean_object* v_inst_4527_, lean_object* v_____do__lift_4528_){
_start:
{
uint8_t v_pu_boxed_4529_; uint8_t v_t_boxed_4530_; lean_object* v_res_4531_; 
v_pu_boxed_4529_ = lean_unbox(v_pu_4524_);
v_t_boxed_4530_ = lean_unbox(v_t_4525_);
v_res_4531_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4529_, v_t_boxed_4530_, v_code_4526_, v_inst_4527_, v_____do__lift_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4532_, uint8_t v_t_4533_, lean_object* v_inst_4534_, lean_object* v_inst_4535_, lean_object* v_inst_4536_, lean_object* v_code_4537_){
_start:
{
lean_object* v_toBind_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___f_4541_; lean_object* v___x_4542_; 
v_toBind_4538_ = lean_ctor_get(v_inst_4535_, 1);
lean_inc(v_toBind_4538_);
lean_dec_ref(v_inst_4535_);
v___x_4539_ = lean_box(v_pu_4532_);
v___x_4540_ = lean_box(v_t_4533_);
v___f_4541_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4541_, 0, v___x_4539_);
lean_closure_set(v___f_4541_, 1, v___x_4540_);
lean_closure_set(v___f_4541_, 2, v_code_4537_);
lean_closure_set(v___f_4541_, 3, v_inst_4534_);
v___x_4542_ = lean_apply_4(v_toBind_4538_, lean_box(0), lean_box(0), v_inst_4536_, v___f_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4543_, lean_object* v_t_4544_, lean_object* v_inst_4545_, lean_object* v_inst_4546_, lean_object* v_inst_4547_, lean_object* v_code_4548_){
_start:
{
uint8_t v_pu_boxed_4549_; uint8_t v_t_boxed_4550_; lean_object* v_res_4551_; 
v_pu_boxed_4549_ = lean_unbox(v_pu_4543_);
v_t_boxed_4550_ = lean_unbox(v_t_4544_);
v_res_4551_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4549_, v_t_boxed_4550_, v_inst_4545_, v_inst_4546_, v_inst_4547_, v_code_4548_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4552_, uint8_t v_pu_4553_, uint8_t v_t_4554_, lean_object* v_inst_4555_, lean_object* v_inst_4556_, lean_object* v_inst_4557_, lean_object* v_code_4558_){
_start:
{
lean_object* v_toBind_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___f_4562_; lean_object* v___x_4563_; 
v_toBind_4559_ = lean_ctor_get(v_inst_4556_, 1);
lean_inc(v_toBind_4559_);
lean_dec_ref(v_inst_4556_);
v___x_4560_ = lean_box(v_pu_4553_);
v___x_4561_ = lean_box(v_t_4554_);
v___f_4562_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4562_, 0, v___x_4560_);
lean_closure_set(v___f_4562_, 1, v___x_4561_);
lean_closure_set(v___f_4562_, 2, v_code_4558_);
lean_closure_set(v___f_4562_, 3, v_inst_4555_);
v___x_4563_ = lean_apply_4(v_toBind_4559_, lean_box(0), lean_box(0), v_inst_4557_, v___f_4562_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4564_, lean_object* v_pu_4565_, lean_object* v_t_4566_, lean_object* v_inst_4567_, lean_object* v_inst_4568_, lean_object* v_inst_4569_, lean_object* v_code_4570_){
_start:
{
uint8_t v_pu_boxed_4571_; uint8_t v_t_boxed_4572_; lean_object* v_res_4573_; 
v_pu_boxed_4571_ = lean_unbox(v_pu_4565_);
v_t_boxed_4572_ = lean_unbox(v_t_4566_);
v_res_4573_ = l_Lean_Compiler_LCNF_normCode(v_m_4564_, v_pu_boxed_4571_, v_t_boxed_4572_, v_inst_4567_, v_inst_4568_, v_inst_4569_, v_code_4570_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4574_, lean_object* v_e_4575_, lean_object* v_s_4576_, uint8_t v_translator_4577_){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4574_, v_s_4576_, v_translator_4577_, v_e_4575_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4581_, lean_object* v_e_4582_, lean_object* v_s_4583_, lean_object* v_translator_4584_, lean_object* v_a_4585_){
_start:
{
uint8_t v_pu_boxed_4586_; uint8_t v_translator_boxed_4587_; lean_object* v_res_4588_; 
v_pu_boxed_4586_ = lean_unbox(v_pu_4581_);
v_translator_boxed_4587_ = lean_unbox(v_translator_4584_);
v_res_4588_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4586_, v_e_4582_, v_s_4583_, v_translator_boxed_4587_);
lean_dec_ref(v_s_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4589_, lean_object* v_e_4590_, lean_object* v_s_4591_, uint8_t v_translator_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4589_, v_e_4590_, v_s_4591_, v_translator_4592_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4599_, lean_object* v_e_4600_, lean_object* v_s_4601_, lean_object* v_translator_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
uint8_t v_pu_boxed_4608_; uint8_t v_translator_boxed_4609_; lean_object* v_res_4610_; 
v_pu_boxed_4608_ = lean_unbox(v_pu_4599_);
v_translator_boxed_4609_ = lean_unbox(v_translator_4602_);
v_res_4610_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4608_, v_e_4600_, v_s_4601_, v_translator_boxed_4609_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
lean_dec_ref(v_s_4601_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4611_, lean_object* v_code_4612_, lean_object* v_s_4613_, uint8_t v_translator_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4611_, v_translator_4614_, v_code_4612_, v_s_4613_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4621_, lean_object* v_code_4622_, lean_object* v_s_4623_, lean_object* v_translator_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
uint8_t v_pu_boxed_4630_; uint8_t v_translator_boxed_4631_; lean_object* v_res_4632_; 
v_pu_boxed_4630_ = lean_unbox(v_pu_4621_);
v_translator_boxed_4631_ = lean_unbox(v_translator_4624_);
v_res_4632_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4630_, v_code_4622_, v_s_4623_, v_translator_boxed_4631_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec_ref(v_s_4623_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4636_){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4639_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4638_, v_a_4636_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4640_, lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4640_);
lean_dec(v_a_4640_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4644_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4655_, lean_object* v_type_4656_, uint8_t v_borrow_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v_a_4665_; lean_object* v___x_4666_; 
v___x_4663_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4664_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4663_, v_a_4659_);
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref(v___x_4664_);
v___x_4666_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4655_, v_a_4665_, v_type_4656_, v_borrow_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4667_, lean_object* v_type_4668_, lean_object* v_borrow_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
uint8_t v_pu_boxed_4675_; uint8_t v_borrow_boxed_4676_; lean_object* v_res_4677_; 
v_pu_boxed_4675_ = lean_unbox(v_pu_4667_);
v_borrow_boxed_4676_ = lean_unbox(v_borrow_4669_);
v_res_4677_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4675_, v_type_4668_, v_borrow_boxed_4676_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4678_){
_start:
{
lean_object* v_config_4680_; lean_object* v___x_4681_; 
v_config_4680_ = lean_ctor_get(v_a_4678_, 0);
lean_inc_ref(v_config_4680_);
v___x_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4681_, 0, v_config_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4682_);
lean_dec_ref(v_a_4682_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4685_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_Lean_Compiler_LCNF_getConfig(v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4697_, lean_object* v_s_4698_, uint8_t v_phase_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v_toCold_4703_; lean_object* v_options_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v_toCold_4703_ = lean_ctor_get(v_a_4700_, 0);
v_options_4704_ = lean_ctor_get(v_toCold_4703_, 2);
v___x_4705_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4704_);
v___x_4706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
lean_ctor_set_uint8(v___x_4706_, sizeof(void*)*1, v_phase_4699_);
v___x_4707_ = lean_st_mk_ref(v_s_4698_);
lean_inc(v_a_4701_);
lean_inc_ref(v_a_4700_);
lean_inc(v___x_4707_);
v___x_4708_ = lean_apply_5(v_x_4697_, v___x_4706_, v___x_4707_, v_a_4700_, v_a_4701_, lean_box(0));
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4717_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4711_ = v___x_4708_;
v_isShared_4712_ = v_isSharedCheck_4717_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4717_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4713_; lean_object* v___x_4715_; 
v___x_4713_ = lean_st_ref_get(v___x_4707_);
lean_dec(v___x_4707_);
lean_dec(v___x_4713_);
if (v_isShared_4712_ == 0)
{
v___x_4715_ = v___x_4711_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4709_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
else
{
lean_dec(v___x_4707_);
return v___x_4708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4718_, lean_object* v_s_4719_, lean_object* v_phase_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
uint8_t v_phase_boxed_4724_; lean_object* v_res_4725_; 
v_phase_boxed_4724_ = lean_unbox(v_phase_4720_);
v_res_4725_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4718_, v_s_4719_, v_phase_boxed_4724_, v_a_4721_, v_a_4722_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4726_, lean_object* v_x_4727_, lean_object* v_s_4728_, uint8_t v_phase_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4727_, v_s_4728_, v_phase_4729_, v_a_4730_, v_a_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4734_, lean_object* v_x_4735_, lean_object* v_s_4736_, lean_object* v_phase_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
uint8_t v_phase_boxed_4741_; lean_object* v_res_4742_; 
v_phase_boxed_4741_ = lean_unbox(v_phase_4737_);
v_res_4742_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4734_, v_x_4735_, v_s_4736_, v_phase_boxed_4741_, v_a_4738_, v_a_4739_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
return v_res_4742_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg(){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object* v___dummy_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4748_, lean_object* v_00_u03b2_4749_, lean_object* v_inst_4750_, lean_object* v_inst_4751_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4753_, lean_object* v_00_u03b2_4754_, lean_object* v_inst_4755_, lean_object* v_inst_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4753_, v_00_u03b2_4754_, v_inst_4755_, v_inst_4756_);
lean_dec_ref(v_inst_4756_);
lean_dec_ref(v_inst_4755_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg(){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object* v___dummy_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec_ref(v_a_4770_);
lean_dec_ref(v_a_4769_);
return v_res_4771_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4775_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4776_ = lean_unsigned_to_nat(14u);
v___x_4777_ = lean_unsigned_to_nat(178u);
v___x_4778_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4779_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4780_ = l_mkPanicMessageWithDecl(v___x_4779_, v___x_4778_, v___x_4777_, v___x_4776_, v___x_4775_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4781_, lean_object* v_inst_4782_, lean_object* v_snd_4783_, lean_object* v_inst_4784_, lean_object* v_s_4785_, lean_object* v_e_4786_){
_start:
{
lean_object* v_fst_4787_; lean_object* v_snd_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4803_; 
v_fst_4787_ = lean_ctor_get(v_s_4785_, 0);
v_snd_4788_ = lean_ctor_get(v_s_4785_, 1);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_s_4785_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4790_ = v_s_4785_;
v_isShared_4791_ = v_isSharedCheck_4803_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_snd_4788_);
lean_inc(v_fst_4787_);
lean_dec(v_s_4785_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4803_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v___y_4794_; lean_object* v___x_4799_; 
lean_inc_n(v_e_4786_, 2);
v___x_4792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4792_, 0, v_e_4786_);
lean_ctor_set(v___x_4792_, 1, v_fst_4787_);
lean_inc_ref(v_inst_4782_);
lean_inc_ref(v_inst_4781_);
v___x_4799_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4781_, v_inst_4782_, v_snd_4783_, v_e_4786_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4801_ = l_panic___redArg(v_inst_4784_, v___x_4800_);
v___y_4794_ = v___x_4801_;
goto v___jp_4793_;
}
else
{
lean_object* v_val_4802_; 
v_val_4802_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_val_4802_);
lean_dec_ref_known(v___x_4799_, 1);
v___y_4794_ = v_val_4802_;
goto v___jp_4793_;
}
v___jp_4793_:
{
lean_object* v___x_4795_; lean_object* v___x_4797_; 
v___x_4795_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4781_, v_inst_4782_, v_snd_4788_, v_e_4786_, v___y_4794_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 1, v___x_4795_);
lean_ctor_set(v___x_4790_, 0, v___x_4792_);
v___x_4797_ = v___x_4790_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4804_, lean_object* v_inst_4805_, lean_object* v_snd_4806_, lean_object* v_inst_4807_, lean_object* v_s_4808_, lean_object* v_e_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4804_, v_inst_4805_, v_snd_4806_, v_inst_4807_, v_s_4808_, v_e_4809_);
lean_dec(v_inst_4807_);
lean_dec(v_snd_4806_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4813_, lean_object* v_inst_4814_, lean_object* v_inst_4815_, lean_object* v_oldState_4816_, lean_object* v_newState_4817_, lean_object* v_x_4818_, lean_object* v_s_4819_){
_start:
{
lean_object* v_fst_4820_; lean_object* v_snd_4821_; lean_object* v_fst_4822_; lean_object* v___f_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v_newEntries_4828_; lean_object* v___x_4829_; 
v_fst_4820_ = lean_ctor_get(v_newState_4817_, 0);
lean_inc_n(v_fst_4820_, 2);
v_snd_4821_ = lean_ctor_get(v_newState_4817_, 1);
lean_inc(v_snd_4821_);
lean_dec_ref(v_newState_4817_);
v_fst_4822_ = lean_ctor_get(v_oldState_4816_, 0);
v___f_4823_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4823_, 0, v_inst_4813_);
lean_closure_set(v___f_4823_, 1, v_inst_4814_);
lean_closure_set(v___f_4823_, 2, v_snd_4821_);
lean_closure_set(v___f_4823_, 3, v_inst_4815_);
v___x_4824_ = l_List_lengthTR___redArg(v_fst_4820_);
v___x_4825_ = l_List_lengthTR___redArg(v_fst_4822_);
v___x_4826_ = lean_nat_sub(v___x_4824_, v___x_4825_);
lean_dec(v___x_4825_);
lean_dec(v___x_4824_);
v___x_4827_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4828_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4820_, v_fst_4820_, v___x_4826_, v___x_4827_);
lean_dec(v_fst_4820_);
v___x_4829_ = l_List_foldl___redArg(v___f_4823_, v_s_4819_, v_newEntries_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4830_, lean_object* v_inst_4831_, lean_object* v_inst_4832_, lean_object* v_oldState_4833_, lean_object* v_newState_4834_, lean_object* v_x_4835_, lean_object* v_s_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4830_, v_inst_4831_, v_inst_4832_, v_oldState_4833_, v_newState_4834_, v_x_4835_, v_s_4836_);
lean_dec(v_x_4835_);
lean_dec_ref(v_oldState_4833_);
return v_res_4837_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4838_);
return v___x_4839_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4841_ = lean_box(0);
v___x_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
lean_ctor_set(v___x_4842_, 1, v___x_4840_);
return v___x_4842_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4844_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4844_, 0, lean_box(0));
lean_closure_set(v___x_4844_, 1, lean_box(0));
lean_closure_set(v___x_4844_, 2, v___x_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4845_, lean_object* v_inst_4846_, lean_object* v_inst_4847_){
_start:
{
lean_object* v___f_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___f_4849_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4849_, 0, v_inst_4845_);
lean_closure_set(v___f_4849_, 1, v_inst_4846_);
lean_closure_set(v___f_4849_, 2, v_inst_4847_);
v___x_4850_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4851_, 0, v___f_4849_);
v___x_4852_ = lean_box(0);
v___x_4853_ = l_Lean_registerEnvExtension___redArg(v___x_4850_, v___x_4851_, v___x_4852_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4853_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4853_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
v_a_4862_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4853_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4853_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4870_, lean_object* v_inst_4871_, lean_object* v_inst_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4870_, v_inst_4871_, v_inst_4872_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4875_, lean_object* v_00_u03b2_4876_, lean_object* v_inst_4877_, lean_object* v_inst_4878_, lean_object* v_inst_4879_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4877_, v_inst_4878_, v_inst_4879_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4882_, lean_object* v_00_u03b2_4883_, lean_object* v_inst_4884_, lean_object* v_inst_4885_, lean_object* v_inst_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4882_, v_00_u03b2_4883_, v_inst_4884_, v_inst_4885_, v_inst_4886_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4889_, lean_object* v_inst_4890_, lean_object* v_inst_4891_, lean_object* v_b_4892_, lean_object* v_x_4893_){
_start:
{
lean_object* v_fst_4894_; lean_object* v_snd_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4904_; 
v_fst_4894_ = lean_ctor_get(v_x_4893_, 0);
v_snd_4895_ = lean_ctor_get(v_x_4893_, 1);
v_isSharedCheck_4904_ = !lean_is_exclusive(v_x_4893_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4897_ = v_x_4893_;
v_isShared_4898_ = v_isSharedCheck_4904_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_snd_4895_);
lean_inc(v_fst_4894_);
lean_dec(v_x_4893_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4904_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4902_; 
lean_inc(v_a_4889_);
v___x_4899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4899_, 0, v_a_4889_);
lean_ctor_set(v___x_4899_, 1, v_fst_4894_);
v___x_4900_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4890_, v_inst_4891_, v_snd_4895_, v_a_4889_, v_b_4892_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 1, v___x_4900_);
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4902_ = v___x_4897_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4899_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v___x_4900_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4905_);
return v___x_4906_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4909_, lean_object* v_inst_4910_, lean_object* v_ext_4911_, lean_object* v_a_4912_, lean_object* v_b_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v___f_4916_; lean_object* v___x_4917_; lean_object* v_env_4918_; lean_object* v_nextMacroScope_4919_; lean_object* v_ngen_4920_; lean_object* v_auxDeclNGen_4921_; lean_object* v_traceState_4922_; lean_object* v_messages_4923_; lean_object* v_infoState_4924_; lean_object* v_snapshotTasks_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4939_; 
v___f_4916_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4916_, 0, v_a_4912_);
lean_closure_set(v___f_4916_, 1, v_inst_4909_);
lean_closure_set(v___f_4916_, 2, v_inst_4910_);
lean_closure_set(v___f_4916_, 3, v_b_4913_);
v___x_4917_ = lean_st_ref_take(v_a_4914_);
v_env_4918_ = lean_ctor_get(v___x_4917_, 0);
v_nextMacroScope_4919_ = lean_ctor_get(v___x_4917_, 1);
v_ngen_4920_ = lean_ctor_get(v___x_4917_, 2);
v_auxDeclNGen_4921_ = lean_ctor_get(v___x_4917_, 3);
v_traceState_4922_ = lean_ctor_get(v___x_4917_, 4);
v_messages_4923_ = lean_ctor_get(v___x_4917_, 6);
v_infoState_4924_ = lean_ctor_get(v___x_4917_, 7);
v_snapshotTasks_4925_ = lean_ctor_get(v___x_4917_, 8);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; 
v_unused_4940_ = lean_ctor_get(v___x_4917_, 5);
lean_dec(v_unused_4940_);
v___x_4927_ = v___x_4917_;
v_isShared_4928_ = v_isSharedCheck_4939_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_snapshotTasks_4925_);
lean_inc(v_infoState_4924_);
lean_inc(v_messages_4923_);
lean_inc(v_traceState_4922_);
lean_inc(v_auxDeclNGen_4921_);
lean_inc(v_ngen_4920_);
lean_inc(v_nextMacroScope_4919_);
lean_inc(v_env_4918_);
lean_dec(v___x_4917_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4939_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v_asyncMode_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v_asyncMode_4929_ = lean_ctor_get(v_ext_4911_, 2);
lean_inc(v_asyncMode_4929_);
v___x_4930_ = lean_box(0);
v___x_4931_ = lean_box(0);
v___x_4932_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4911_, v_env_4918_, v___f_4916_, v_asyncMode_4929_, v___x_4931_);
lean_dec(v_asyncMode_4929_);
v___x_4933_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 5, v___x_4933_);
lean_ctor_set(v___x_4927_, 0, v___x_4932_);
v___x_4935_ = v___x_4927_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4932_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v_nextMacroScope_4919_);
lean_ctor_set(v_reuseFailAlloc_4938_, 2, v_ngen_4920_);
lean_ctor_set(v_reuseFailAlloc_4938_, 3, v_auxDeclNGen_4921_);
lean_ctor_set(v_reuseFailAlloc_4938_, 4, v_traceState_4922_);
lean_ctor_set(v_reuseFailAlloc_4938_, 5, v___x_4933_);
lean_ctor_set(v_reuseFailAlloc_4938_, 6, v_messages_4923_);
lean_ctor_set(v_reuseFailAlloc_4938_, 7, v_infoState_4924_);
lean_ctor_set(v_reuseFailAlloc_4938_, 8, v_snapshotTasks_4925_);
v___x_4935_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = lean_st_ref_put(v_a_4914_, v___x_4935_);
v___x_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4930_);
return v___x_4937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4941_, lean_object* v_inst_4942_, lean_object* v_ext_4943_, lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4941_, v_inst_4942_, v_ext_4943_, v_a_4944_, v_b_4945_, v_a_4946_);
lean_dec(v_a_4946_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4949_, lean_object* v_00_u03b2_4950_, lean_object* v_inst_4951_, lean_object* v_inst_4952_, lean_object* v_inst_4953_, lean_object* v_ext_4954_, lean_object* v_a_4955_, lean_object* v_b_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v___x_4960_; 
v___x_4960_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4951_, v_inst_4952_, v_ext_4954_, v_a_4955_, v_b_4956_, v_a_4958_);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4961_, lean_object* v_00_u03b2_4962_, lean_object* v_inst_4963_, lean_object* v_inst_4964_, lean_object* v_inst_4965_, lean_object* v_ext_4966_, lean_object* v_a_4967_, lean_object* v_b_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4961_, v_00_u03b2_4962_, v_inst_4963_, v_inst_4964_, v_inst_4965_, v_ext_4966_, v_a_4967_, v_b_4968_, v_a_4969_, v_a_4970_);
lean_dec(v_a_4970_);
lean_dec_ref(v_a_4969_);
lean_dec(v_inst_4965_);
return v_res_4972_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_4973_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4974_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0);
v___x_4975_ = lean_box(0);
v___x_4976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
lean_ctor_set(v___x_4976_, 1, v___x_4974_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4977_, lean_object* v_inst_4978_, lean_object* v_ext_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v_env_4985_; lean_object* v_asyncMode_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v_snd_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4983_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1);
v___x_4984_ = lean_st_ref_get(v_a_4981_);
v_env_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc_ref(v_env_4985_);
lean_dec(v___x_4984_);
v_asyncMode_4986_ = lean_ctor_get(v_ext_4979_, 2);
v___x_4987_ = lean_box(0);
v___x_4988_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4983_, v_ext_4979_, v_env_4985_, v_asyncMode_4986_, v___x_4987_);
v_snd_4989_ = lean_ctor_get(v___x_4988_, 1);
lean_inc(v_snd_4989_);
lean_dec(v___x_4988_);
v___x_4990_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4977_, v_inst_4978_, v_snd_4989_, v_a_4980_);
lean_dec(v_snd_4989_);
v___x_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4992_, lean_object* v_inst_4993_, lean_object* v_ext_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4992_, v_inst_4993_, v_ext_4994_, v_a_4995_, v_a_4996_);
lean_dec(v_a_4996_);
lean_dec_ref(v_ext_4994_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4999_, lean_object* v_00_u03b2_5000_, lean_object* v_inst_5001_, lean_object* v_inst_5002_, lean_object* v_inst_5003_, lean_object* v_ext_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5001_, v_inst_5002_, v_ext_5004_, v_a_5005_, v_a_5007_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5010_, lean_object* v_00_u03b2_5011_, lean_object* v_inst_5012_, lean_object* v_inst_5013_, lean_object* v_inst_5014_, lean_object* v_ext_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5010_, v_00_u03b2_5011_, v_inst_5012_, v_inst_5013_, v_inst_5014_, v_ext_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
lean_dec_ref(v_ext_5015_);
lean_dec(v_inst_5014_);
return v_res_5020_;
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
