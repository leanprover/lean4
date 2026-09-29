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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lean_takeNewEntries___redArg(lean_object*, lean_object*);
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
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_370_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_370_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_370_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_370_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_lctx_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_368_; 
v_lctx_353_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_347_, 1);
lean_dec(v_unused_369_);
v___x_355_ = v___x_347_;
v_isShared_356_ = v_isSharedCheck_368_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_lctx_353_);
lean_dec(v___x_347_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_368_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_357_ = lean_unbox(v_a_349_);
lean_dec(v_a_349_);
v___x_358_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_353_, v___x_357_);
lean_dec_ref(v_lctx_353_);
v___x_359_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_342_);
v___x_360_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v_env_346_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_ctor_set(v___x_361_, 2, v___x_358_);
lean_ctor_set(v___x_361_, 3, v___x_359_);
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
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_363_);
v___x_365_ = v___x_351_;
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
lean_dec(v___x_347_);
lean_dec_ref(v_env_346_);
lean_dec_ref(v_msgData_339_);
v_a_371_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_348_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_348_);
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
lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_ref_394_ = lean_ctor_get(v___y_391_, 2);
v___x_395_ = lean_st_ref_get(v___y_392_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
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
lean_object* v_lctx_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_419_; 
v_lctx_403_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_397_, 1);
lean_dec(v_unused_420_);
v___x_405_ = v___x_397_;
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_lctx_403_);
lean_dec(v___x_397_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_407_ = lean_unbox(v_a_399_);
lean_dec(v_a_399_);
v___x_408_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_403_, v___x_407_);
lean_dec_ref(v_lctx_403_);
v___x_409_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_391_);
v___x_410_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_396_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_ctor_set(v___x_411_, 2, v___x_408_);
lean_ctor_set(v___x_411_, 3, v___x_409_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 3);
lean_ctor_set(v___x_405_, 1, v_msg_388_);
lean_ctor_set(v___x_405_, 0, v___x_411_);
v___x_413_ = v___x_405_;
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
lean_inc(v_ref_394_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_ref_394_);
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
lean_dec_ref(v_env_396_);
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
lean_object* v___x_495_; lean_object* v_lctx_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_561_; 
v___x_495_ = lean_st_ref_get(v_a_491_);
v_lctx_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v___x_495_, 1);
lean_dec(v_unused_562_);
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_561_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_lctx_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_561_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_490_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_552_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_552_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_552_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_552_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___y_506_; lean_object* v___y_520_; lean_object* v___y_535_; uint8_t v___x_549_; 
v___x_549_ = lean_unbox(v_a_501_);
if (v___x_549_ == 0)
{
lean_object* v_letDeclsPure_550_; 
v_letDeclsPure_550_ = lean_ctor_get(v_lctx_496_, 2);
lean_inc_ref(v_letDeclsPure_550_);
v___y_535_ = v_letDeclsPure_550_;
goto v___jp_534_;
}
else
{
lean_object* v_letDeclsImpure_551_; 
v_letDeclsImpure_551_ = lean_ctor_get(v_lctx_496_, 3);
lean_inc_ref(v_letDeclsImpure_551_);
v___y_535_ = v_letDeclsImpure_551_;
goto v___jp_534_;
}
v___jp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_506_, v_fvarId_489_);
lean_dec_ref(v___y_506_);
if (lean_obj_tag(v___x_507_) == 1)
{
lean_object* v_val_508_; lean_object* v_type_509_; lean_object* v___x_511_; 
lean_del_object(v___x_498_);
lean_dec(v_fvarId_489_);
v_val_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_507_, 1);
v_type_509_ = lean_ctor_get(v_val_508_, 3);
lean_inc_ref(v_type_509_);
lean_dec(v_val_508_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v_type_509_);
v___x_511_ = v___x_503_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_type_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v___x_507_);
lean_del_object(v___x_503_);
v___x_513_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_514_ = l_Lean_MessageData_ofName(v_fvarId_489_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 7);
lean_ctor_set(v___x_498_, 1, v___x_514_);
lean_ctor_set(v___x_498_, 0, v___x_513_);
v___x_516_ = v___x_498_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_518_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_516_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_517_;
}
}
}
v___jp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_520_, v_fvarId_489_);
lean_dec_ref(v___y_520_);
if (lean_obj_tag(v___x_521_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_del_object(v___x_503_);
lean_dec(v_a_501_);
lean_del_object(v___x_498_);
lean_dec_ref(v_lctx_496_);
lean_dec(v_fvarId_489_);
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
v___x_531_ = lean_unbox(v_a_501_);
lean_dec(v_a_501_);
if (v___x_531_ == 0)
{
lean_object* v_funDeclsPure_532_; 
v_funDeclsPure_532_ = lean_ctor_get(v_lctx_496_, 4);
lean_inc_ref(v_funDeclsPure_532_);
lean_dec_ref(v_lctx_496_);
v___y_506_ = v_funDeclsPure_532_;
goto v___jp_505_;
}
else
{
lean_object* v_funDeclsImpure_533_; 
v_funDeclsImpure_533_ = lean_ctor_get(v_lctx_496_, 5);
lean_inc_ref(v_funDeclsImpure_533_);
lean_dec_ref(v_lctx_496_);
v___y_506_ = v_funDeclsImpure_533_;
goto v___jp_505_;
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_535_, v_fvarId_489_);
lean_dec_ref(v___y_535_);
if (lean_obj_tag(v___x_536_) == 1)
{
lean_object* v_val_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
lean_del_object(v___x_503_);
lean_dec(v_a_501_);
lean_del_object(v___x_498_);
lean_dec_ref(v_lctx_496_);
lean_dec(v_fvarId_489_);
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
v___x_546_ = lean_unbox(v_a_501_);
if (v___x_546_ == 0)
{
lean_object* v_paramsPure_547_; 
v_paramsPure_547_ = lean_ctor_get(v_lctx_496_, 0);
lean_inc_ref(v_paramsPure_547_);
v___y_520_ = v_paramsPure_547_;
goto v___jp_519_;
}
else
{
lean_object* v_paramsImpure_548_; 
v_paramsImpure_548_ = lean_ctor_get(v_lctx_496_, 1);
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
lean_del_object(v___x_498_);
lean_dec_ref(v_lctx_496_);
lean_dec(v_fvarId_489_);
v_a_553_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_500_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_500_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Compiler_LCNF_getType(v_fvarId_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_571_, v_a_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_574_, v_m_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_m_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_578_, lean_object* v_a_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_579_, v_x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_582_, lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_582_, v_a_583_, v_x_584_);
lean_dec(v_x_584_);
lean_dec(v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; lean_object* v_lctx_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_658_; 
v___x_592_ = lean_st_ref_get(v_a_588_);
v_lctx_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v___x_592_, 1);
lean_dec(v_unused_659_);
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_658_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_lctx_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_658_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_587_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_649_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_649_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_649_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_649_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___y_603_; lean_object* v___y_617_; lean_object* v___y_632_; uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_a_598_);
if (v___x_646_ == 0)
{
lean_object* v_letDeclsPure_647_; 
v_letDeclsPure_647_ = lean_ctor_get(v_lctx_593_, 2);
lean_inc_ref(v_letDeclsPure_647_);
v___y_632_ = v_letDeclsPure_647_;
goto v___jp_631_;
}
else
{
lean_object* v_letDeclsImpure_648_; 
v_letDeclsImpure_648_ = lean_ctor_get(v_lctx_593_, 3);
lean_inc_ref(v_letDeclsImpure_648_);
v___y_632_ = v_letDeclsImpure_648_;
goto v___jp_631_;
}
v___jp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_603_, v_fvarId_586_);
lean_dec_ref(v___y_603_);
if (lean_obj_tag(v___x_604_) == 1)
{
lean_object* v_val_605_; lean_object* v_binderName_606_; lean_object* v___x_608_; 
lean_del_object(v___x_595_);
lean_dec(v_fvarId_586_);
v_val_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_604_, 1);
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
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
lean_dec(v___x_604_);
lean_del_object(v___x_600_);
v___x_610_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_611_ = l_Lean_MessageData_ofName(v_fvarId_586_);
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 7);
lean_ctor_set(v___x_595_, 1, v___x_611_);
lean_ctor_set(v___x_595_, 0, v___x_610_);
v___x_613_ = v___x_595_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_613_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
return v___x_614_;
}
}
}
v___jp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_617_, v_fvarId_586_);
lean_dec_ref(v___y_617_);
if (lean_obj_tag(v___x_618_) == 1)
{
lean_object* v_val_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
lean_del_object(v___x_595_);
lean_dec_ref(v_lctx_593_);
lean_dec(v_fvarId_586_);
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
v___x_628_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
if (v___x_628_ == 0)
{
lean_object* v_funDeclsPure_629_; 
v_funDeclsPure_629_ = lean_ctor_get(v_lctx_593_, 4);
lean_inc_ref(v_funDeclsPure_629_);
lean_dec_ref(v_lctx_593_);
v___y_603_ = v_funDeclsPure_629_;
goto v___jp_602_;
}
else
{
lean_object* v_funDeclsImpure_630_; 
v_funDeclsImpure_630_ = lean_ctor_get(v_lctx_593_, 5);
lean_inc_ref(v_funDeclsImpure_630_);
lean_dec_ref(v_lctx_593_);
v___y_603_ = v_funDeclsImpure_630_;
goto v___jp_602_;
}
}
}
v___jp_631_:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_632_, v_fvarId_586_);
lean_dec_ref(v___y_632_);
if (lean_obj_tag(v___x_633_) == 1)
{
lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
lean_del_object(v___x_595_);
lean_dec_ref(v_lctx_593_);
lean_dec(v_fvarId_586_);
v_val_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_642_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_binderName_638_; lean_object* v___x_640_; 
v_binderName_638_ = lean_ctor_get(v_val_634_, 1);
lean_inc(v_binderName_638_);
lean_dec(v_val_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 0);
lean_ctor_set(v___x_636_, 0, v_binderName_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_binderName_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
uint8_t v___x_643_; 
lean_dec(v___x_633_);
v___x_643_ = lean_unbox(v_a_598_);
if (v___x_643_ == 0)
{
lean_object* v_paramsPure_644_; 
v_paramsPure_644_ = lean_ctor_get(v_lctx_593_, 0);
lean_inc_ref(v_paramsPure_644_);
v___y_617_ = v_paramsPure_644_;
goto v___jp_616_;
}
else
{
lean_object* v_paramsImpure_645_; 
v_paramsImpure_645_ = lean_ctor_get(v_lctx_593_, 1);
lean_inc_ref(v_paramsImpure_645_);
v___y_617_ = v_paramsImpure_645_;
goto v___jp_616_;
}
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_del_object(v___x_595_);
lean_dec_ref(v_lctx_593_);
lean_dec(v_fvarId_586_);
v_a_650_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_597_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_597_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_667_, lean_object* v_fvarId_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___y_673_; 
v___x_671_ = lean_st_ref_get(v_a_669_);
if (v_pu_667_ == 0)
{
lean_object* v_lctx_676_; lean_object* v_paramsPure_677_; 
v_lctx_676_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_lctx_676_);
lean_dec(v___x_671_);
v_paramsPure_677_ = lean_ctor_get(v_lctx_676_, 0);
lean_inc_ref(v_paramsPure_677_);
lean_dec_ref(v_lctx_676_);
v___y_673_ = v_paramsPure_677_;
goto v___jp_672_;
}
else
{
lean_object* v_lctx_678_; lean_object* v_paramsImpure_679_; 
v_lctx_678_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_lctx_678_);
lean_dec(v___x_671_);
v_paramsImpure_679_ = lean_ctor_get(v_lctx_678_, 1);
lean_inc_ref(v_paramsImpure_679_);
lean_dec_ref(v_lctx_678_);
v___y_673_ = v_paramsImpure_679_;
goto v___jp_672_;
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_673_, v_fvarId_668_);
lean_dec_ref(v___y_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_680_, lean_object* v_fvarId_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
uint8_t v_pu_boxed_684_; lean_object* v_res_685_; 
v_pu_boxed_684_ = lean_unbox(v_pu_680_);
v_res_685_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_684_, v_fvarId_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec(v_fvarId_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_686_, lean_object* v_fvarId_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_686_, v_fvarId_687_, v_a_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_694_, lean_object* v_fvarId_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
uint8_t v_pu_boxed_701_; lean_object* v_res_702_; 
v_pu_boxed_701_ = lean_unbox(v_pu_694_);
v_res_702_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_701_, v_fvarId_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_fvarId_695_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_703_, lean_object* v_fvarId_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___y_709_; 
v___x_707_ = lean_st_ref_get(v_a_705_);
if (v_pu_703_ == 0)
{
lean_object* v_lctx_712_; lean_object* v_letDeclsPure_713_; 
v_lctx_712_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_lctx_712_);
lean_dec(v___x_707_);
v_letDeclsPure_713_ = lean_ctor_get(v_lctx_712_, 2);
lean_inc_ref(v_letDeclsPure_713_);
lean_dec_ref(v_lctx_712_);
v___y_709_ = v_letDeclsPure_713_;
goto v___jp_708_;
}
else
{
lean_object* v_lctx_714_; lean_object* v_letDeclsImpure_715_; 
v_lctx_714_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_lctx_714_);
lean_dec(v___x_707_);
v_letDeclsImpure_715_ = lean_ctor_get(v_lctx_714_, 3);
lean_inc_ref(v_letDeclsImpure_715_);
lean_dec_ref(v_lctx_714_);
v___y_709_ = v_letDeclsImpure_715_;
goto v___jp_708_;
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_709_, v_fvarId_704_);
lean_dec_ref(v___y_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_716_, lean_object* v_fvarId_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
uint8_t v_pu_boxed_720_; lean_object* v_res_721_; 
v_pu_boxed_720_ = lean_unbox(v_pu_716_);
v_res_721_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_720_, v_fvarId_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec(v_fvarId_717_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_722_, lean_object* v_fvarId_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_722_, v_fvarId_723_, v_a_725_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_730_, lean_object* v_fvarId_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
uint8_t v_pu_boxed_737_; lean_object* v_res_738_; 
v_pu_boxed_737_ = lean_unbox(v_pu_730_);
v_res_738_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_737_, v_fvarId_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_fvarId_731_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_739_, lean_object* v_fvarId_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; lean_object* v___y_745_; 
v___x_743_ = lean_st_ref_get(v_a_741_);
if (v_pu_739_ == 0)
{
lean_object* v_lctx_748_; lean_object* v_funDeclsPure_749_; 
v_lctx_748_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_lctx_748_);
lean_dec(v___x_743_);
v_funDeclsPure_749_ = lean_ctor_get(v_lctx_748_, 4);
lean_inc_ref(v_funDeclsPure_749_);
lean_dec_ref(v_lctx_748_);
v___y_745_ = v_funDeclsPure_749_;
goto v___jp_744_;
}
else
{
lean_object* v_lctx_750_; lean_object* v_funDeclsImpure_751_; 
v_lctx_750_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_lctx_750_);
lean_dec(v___x_743_);
v_funDeclsImpure_751_ = lean_ctor_get(v_lctx_750_, 5);
lean_inc_ref(v_funDeclsImpure_751_);
lean_dec_ref(v_lctx_750_);
v___y_745_ = v_funDeclsImpure_751_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_745_, v_fvarId_740_);
lean_dec_ref(v___y_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_752_, lean_object* v_fvarId_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
uint8_t v_pu_boxed_756_; lean_object* v_res_757_; 
v_pu_boxed_756_ = lean_unbox(v_pu_752_);
v_res_757_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_756_, v_fvarId_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec(v_fvarId_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_758_, lean_object* v_fvarId_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_758_, v_fvarId_759_, v_a_761_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_766_, lean_object* v_fvarId_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
uint8_t v_pu_boxed_773_; lean_object* v_res_774_; 
v_pu_boxed_773_ = lean_unbox(v_pu_766_);
v_res_774_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_773_, v_fvarId_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_fvarId_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_775_, lean_object* v_fvarId_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_800_; 
v___x_779_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_775_, v_fvarId_776_, v_a_777_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_800_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_800_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_800_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
if (lean_obj_tag(v_a_780_) == 1)
{
lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_795_; 
v_val_784_ = lean_ctor_get(v_a_780_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_780_);
if (v_isSharedCheck_795_ == 0)
{
v___x_786_ = v_a_780_;
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v_a_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_value_788_; lean_object* v___x_790_; 
v_value_788_ = lean_ctor_get(v_val_784_, 3);
lean_inc(v_value_788_);
lean_dec(v_val_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_value_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_value_788_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_790_);
v___x_792_ = v___x_782_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v_a_780_);
v___x_796_ = lean_box(0);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_796_);
v___x_798_ = v___x_782_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_801_, lean_object* v_fvarId_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_pu_boxed_805_; lean_object* v_res_806_; 
v_pu_boxed_805_ = lean_unbox(v_pu_801_);
v_res_806_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_805_, v_fvarId_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec(v_fvarId_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_807_, lean_object* v_fvarId_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_807_, v_fvarId_808_, v_a_810_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_815_, lean_object* v_fvarId_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
uint8_t v_pu_boxed_822_; lean_object* v_res_823_; 
v_pu_boxed_822_ = lean_unbox(v_pu_815_);
v_res_823_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_822_, v_fvarId_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_fvarId_816_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
uint8_t v___x_832_; lean_object* v___x_833_; 
v___x_832_ = 0;
v___x_833_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_832_, v_fvarId_824_, v_a_825_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_861_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_861_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_861_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_861_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
if (lean_obj_tag(v_a_834_) == 1)
{
lean_object* v_val_838_; 
v_val_838_ = lean_ctor_get(v_a_834_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v_a_834_, 1);
if (lean_obj_tag(v_val_838_) == 3)
{
lean_object* v_declName_839_; lean_object* v___x_840_; lean_object* v_env_847_; uint8_t v___x_848_; lean_object* v___x_849_; 
v_declName_839_ = lean_ctor_get(v_val_838_, 0);
lean_inc(v_declName_839_);
lean_dec_ref_known(v_val_838_, 3);
v___x_840_ = lean_st_ref_get(v_a_826_);
v_env_847_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_env_847_);
lean_dec(v___x_840_);
v___x_848_ = 0;
v___x_849_ = l_Lean_Environment_find_x3f(v_env_847_, v_declName_839_, v___x_848_);
if (lean_obj_tag(v___x_849_) == 1)
{
lean_object* v_val_850_; 
v_val_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___x_849_, 1);
if (lean_obj_tag(v_val_850_) == 6)
{
lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_859_; 
lean_del_object(v___x_836_);
v_isSharedCheck_859_ = !lean_is_exclusive(v_val_850_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v_val_850_, 0);
lean_dec(v_unused_860_);
v___x_852_ = v_val_850_;
v_isShared_853_ = v_isSharedCheck_859_;
goto v_resetjp_851_;
}
else
{
lean_dec(v_val_850_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_859_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = 1;
v___x_855_ = lean_box(v___x_854_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 0);
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_dec(v_val_850_);
goto v___jp_841_;
}
}
else
{
lean_dec(v___x_849_);
goto v___jp_841_;
}
v___jp_841_:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = 0;
v___x_843_ = lean_box(v___x_842_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_dec(v_val_838_);
lean_del_object(v___x_836_);
goto v___jp_828_;
}
}
else
{
lean_del_object(v___x_836_);
lean_dec(v_a_834_);
goto v___jp_828_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_833_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_833_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
v___jp_828_:
{
uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = 0;
v___x_830_ = lean_box(v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_870_, v_a_871_, v_a_872_);
lean_dec(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_fvarId_870_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_875_, v_a_877_, v_a_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_fvarId_882_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
if (lean_obj_tag(v_arg_889_) == 1)
{
lean_object* v_fvarId_893_; lean_object* v___x_894_; 
v_fvarId_893_ = lean_ctor_get(v_arg_889_, 0);
v___x_894_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_893_, v_a_890_, v_a_891_);
return v___x_894_;
}
else
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = 0;
v___x_896_ = lean_box(v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
lean_dec(v_arg_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_903_, lean_object* v_arg_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_904_, v_a_906_, v_a_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_911_, lean_object* v_arg_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
uint8_t v_pu_boxed_918_; lean_object* v_res_919_; 
v_pu_boxed_918_ = lean_unbox(v_pu_911_);
v_res_919_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_918_, v_arg_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_arg_912_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_923_, lean_object* v_fvarId_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_943_; 
v___x_930_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_923_, v_fvarId_924_, v_a_926_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_943_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 1)
{
lean_object* v_val_935_; lean_object* v___x_937_; 
lean_dec(v_fvarId_924_);
v_val_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_a_931_, 1);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_val_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_val_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_del_object(v___x_933_);
lean_dec(v_a_931_);
v___x_939_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_940_ = l_Lean_MessageData_ofName(v_fvarId_924_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_941_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_944_, lean_object* v_fvarId_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
uint8_t v_pu_boxed_951_; lean_object* v_res_952_; 
v_pu_boxed_951_ = lean_unbox(v_pu_944_);
v_res_952_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_951_, v_fvarId_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_952_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_956_, lean_object* v_fvarId_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_976_; 
v___x_963_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_956_, v_fvarId_957_, v_a_959_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_976_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
if (lean_obj_tag(v_a_964_) == 1)
{
lean_object* v_val_968_; lean_object* v___x_970_; 
lean_dec(v_fvarId_957_);
v_val_968_ = lean_ctor_get(v_a_964_, 0);
lean_inc(v_val_968_);
lean_dec_ref_known(v_a_964_, 1);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_val_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_val_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_del_object(v___x_966_);
lean_dec(v_a_964_);
v___x_972_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_973_ = l_Lean_MessageData_ofName(v_fvarId_957_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_974_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_977_, lean_object* v_fvarId_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
uint8_t v_pu_boxed_984_; lean_object* v_res_985_; 
v_pu_boxed_984_ = lean_unbox(v_pu_977_);
v_res_985_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_984_, v_fvarId_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_985_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_989_, lean_object* v_fvarId_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1009_; 
v___x_996_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_989_, v_fvarId_990_, v_a_992_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1009_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1009_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
if (lean_obj_tag(v_a_997_) == 1)
{
lean_object* v_val_1001_; lean_object* v___x_1003_; 
lean_dec(v_fvarId_990_);
v_val_1001_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v_a_997_, 1);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_val_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_val_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_999_);
lean_dec(v_a_997_);
v___x_1005_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1006_ = l_Lean_MessageData_ofName(v_fvarId_990_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1007_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1010_, lean_object* v_fvarId_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
uint8_t v_pu_boxed_1017_; lean_object* v_res_1018_; 
v_pu_boxed_1017_ = lean_unbox(v_pu_1010_);
v_res_1018_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1017_, v_fvarId_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v_lctx_1023_; lean_object* v_nextIdx_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1035_; 
v___x_1022_ = lean_st_ref_take(v_a_1020_);
v_lctx_1023_ = lean_ctor_get(v___x_1022_, 0);
v_nextIdx_1024_ = lean_ctor_get(v___x_1022_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1026_ = v___x_1022_;
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_nextIdx_1024_);
lean_inc(v_lctx_1023_);
lean_dec(v___x_1022_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_apply_1(v_f_1019_, v_lctx_1023_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_nextIdx_1024_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_st_ref_put(v_a_1020_, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1028_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1036_, v_a_1037_);
lean_dec(v_a_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_lctx_1047_; lean_object* v_nextIdx_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1059_; 
v___x_1046_ = lean_st_ref_take(v_a_1042_);
v_lctx_1047_ = lean_ctor_get(v___x_1046_, 0);
v_nextIdx_1048_ = lean_ctor_get(v___x_1046_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1050_ = v___x_1046_;
v_isShared_1051_ = v_isSharedCheck_1059_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_nextIdx_1048_);
lean_inc(v_lctx_1047_);
lean_dec(v___x_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1059_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_apply_1(v_f_1040_, v_lctx_1047_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_nextIdx_1048_);
v___x_1055_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_st_ref_put(v_a_1042_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1052_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1067_, lean_object* v_decl_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v_lctx_1072_; lean_object* v_nextIdx_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1084_; 
v___x_1071_ = lean_st_ref_take(v_a_1069_);
v_lctx_1072_ = lean_ctor_get(v___x_1071_, 0);
v_nextIdx_1073_ = lean_ctor_get(v___x_1071_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1075_ = v___x_1071_;
v_isShared_1076_ = v_isSharedCheck_1084_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_nextIdx_1073_);
lean_inc(v_lctx_1072_);
lean_dec(v___x_1071_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1084_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1067_, v_lctx_1072_, v_decl_1068_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_nextIdx_1073_);
v___x_1080_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_st_ref_put(v_a_1069_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1077_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1085_, lean_object* v_decl_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
uint8_t v_pu_boxed_1089_; lean_object* v_res_1090_; 
v_pu_boxed_1089_ = lean_unbox(v_pu_1085_);
v_res_1090_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1089_, v_decl_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_decl_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1091_, lean_object* v_decl_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1091_, v_decl_1092_, v_a_1094_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1099_, lean_object* v_decl_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
uint8_t v_pu_boxed_1106_; lean_object* v_res_1107_; 
v_pu_boxed_1106_ = lean_unbox(v_pu_1099_);
v_res_1107_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1106_, v_decl_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_decl_1100_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1108_, lean_object* v_decl_1109_, uint8_t v_recursive_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_lctx_1114_; lean_object* v_nextIdx_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1126_; 
v___x_1113_ = lean_st_ref_take(v_a_1111_);
v_lctx_1114_ = lean_ctor_get(v___x_1113_, 0);
v_nextIdx_1115_ = lean_ctor_get(v___x_1113_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1117_ = v___x_1113_;
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_nextIdx_1115_);
lean_inc(v_lctx_1114_);
lean_dec(v___x_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1108_, v_lctx_1114_, v_decl_1109_, v_recursive_1110_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_nextIdx_1115_);
v___x_1122_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_st_ref_put(v_a_1111_, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1119_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1127_, lean_object* v_decl_1128_, lean_object* v_recursive_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint8_t v_pu_boxed_1132_; uint8_t v_recursive_boxed_1133_; lean_object* v_res_1134_; 
v_pu_boxed_1132_ = lean_unbox(v_pu_1127_);
v_recursive_boxed_1133_ = lean_unbox(v_recursive_1129_);
v_res_1134_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1132_, v_decl_1128_, v_recursive_boxed_1133_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_decl_1128_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1135_, lean_object* v_decl_1136_, uint8_t v_recursive_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1135_, v_decl_1136_, v_recursive_1137_, v_a_1139_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1144_, lean_object* v_decl_1145_, lean_object* v_recursive_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_pu_boxed_1152_; uint8_t v_recursive_boxed_1153_; lean_object* v_res_1154_; 
v_pu_boxed_1152_ = lean_unbox(v_pu_1144_);
v_recursive_boxed_1153_ = lean_unbox(v_recursive_1146_);
v_res_1154_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1152_, v_decl_1145_, v_recursive_boxed_1153_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec_ref(v_decl_1145_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1155_, lean_object* v_code_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v_lctx_1160_; lean_object* v_nextIdx_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1172_; 
v___x_1159_ = lean_st_ref_take(v_a_1157_);
v_lctx_1160_ = lean_ctor_get(v___x_1159_, 0);
v_nextIdx_1161_ = lean_ctor_get(v___x_1159_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1163_ = v___x_1159_;
v_isShared_1164_ = v_isSharedCheck_1172_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_nextIdx_1161_);
lean_inc(v_lctx_1160_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1172_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1155_, v_code_1156_, v_lctx_1160_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1166_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_nextIdx_1161_);
v___x_1168_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_st_ref_put(v_a_1157_, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1165_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1173_, lean_object* v_code_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
uint8_t v_pu_boxed_1177_; lean_object* v_res_1178_; 
v_pu_boxed_1177_ = lean_unbox(v_pu_1173_);
v_res_1178_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1177_, v_code_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_code_1174_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1179_, lean_object* v_code_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1179_, v_code_1180_, v_a_1182_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1187_, lean_object* v_code_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
uint8_t v_pu_boxed_1194_; lean_object* v_res_1195_; 
v_pu_boxed_1194_ = lean_unbox(v_pu_1187_);
v_res_1195_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1194_, v_code_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec_ref(v_code_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1196_, lean_object* v_param_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v_lctx_1201_; lean_object* v_nextIdx_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1213_; 
v___x_1200_ = lean_st_ref_take(v_a_1198_);
v_lctx_1201_ = lean_ctor_get(v___x_1200_, 0);
v_nextIdx_1202_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1213_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_nextIdx_1202_);
lean_inc(v_lctx_1201_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1213_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1196_, v_lctx_1201_, v_param_1197_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_nextIdx_1202_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_put(v_a_1198_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1206_);
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1214_, lean_object* v_param_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
uint8_t v_pu_boxed_1218_; lean_object* v_res_1219_; 
v_pu_boxed_1218_ = lean_unbox(v_pu_1214_);
v_res_1219_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1218_, v_param_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_param_1215_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1220_, lean_object* v_param_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1220_, v_param_1221_, v_a_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1228_, lean_object* v_param_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
uint8_t v_pu_boxed_1235_; lean_object* v_res_1236_; 
v_pu_boxed_1235_ = lean_unbox(v_pu_1228_);
v_res_1236_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1235_, v_param_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec_ref(v_param_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1237_, lean_object* v_params_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_lctx_1242_; lean_object* v_nextIdx_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1254_; 
v___x_1241_ = lean_st_ref_take(v_a_1239_);
v_lctx_1242_ = lean_ctor_get(v___x_1241_, 0);
v_nextIdx_1243_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1245_ = v___x_1241_;
v_isShared_1246_ = v_isSharedCheck_1254_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_nextIdx_1243_);
lean_inc(v_lctx_1242_);
lean_dec(v___x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1254_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1237_, v_lctx_1242_, v_params_1238_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1248_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_nextIdx_1243_);
v___x_1250_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_st_ref_put(v_a_1239_, v___x_1250_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1247_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1255_, lean_object* v_params_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_pu_boxed_1259_; lean_object* v_res_1260_; 
v_pu_boxed_1259_ = lean_unbox(v_pu_1255_);
v_res_1260_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1259_, v_params_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_params_1256_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1261_, lean_object* v_params_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1261_, v_params_1262_, v_a_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1269_, lean_object* v_params_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
uint8_t v_pu_boxed_1276_; lean_object* v_res_1277_; 
v_pu_boxed_1276_ = lean_unbox(v_pu_1269_);
v_res_1277_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1276_, v_params_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec_ref(v_params_1270_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1278_, lean_object* v_decl_1279_, lean_object* v_a_1280_){
_start:
{
switch(lean_obj_tag(v_decl_1279_))
{
case 0:
{
lean_object* v_decl_1282_; lean_object* v___x_1283_; 
v_decl_1282_ = lean_ctor_get(v_decl_1279_, 0);
v___x_1283_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1278_, v_decl_1282_, v_a_1280_);
return v___x_1283_;
}
case 1:
{
lean_object* v_decl_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; 
v_decl_1284_ = lean_ctor_get(v_decl_1279_, 0);
v___x_1285_ = 1;
v___x_1286_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1278_, v_decl_1284_, v___x_1285_, v_a_1280_);
return v___x_1286_;
}
case 2:
{
lean_object* v_decl_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; 
v_decl_1287_ = lean_ctor_get(v_decl_1279_, 0);
v___x_1288_ = 1;
v___x_1289_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1278_, v_decl_1287_, v___x_1288_, v_a_1280_);
return v___x_1289_;
}
default: 
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1292_, lean_object* v_decl_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
uint8_t v_pu_boxed_1296_; lean_object* v_res_1297_; 
v_pu_boxed_1296_ = lean_unbox(v_pu_1292_);
v_res_1297_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1296_, v_decl_1293_, v_a_1294_);
lean_dec(v_a_1294_);
lean_dec_ref(v_decl_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1298_, lean_object* v_decl_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1298_, v_decl_1299_, v_a_1301_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1306_, lean_object* v_decl_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
uint8_t v_pu_boxed_1313_; lean_object* v_res_1314_; 
v_pu_boxed_1313_ = lean_unbox(v_pu_1306_);
v_res_1314_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1313_, v_decl_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v_decl_1307_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1315_, lean_object* v_as_1316_, size_t v_i_1317_, size_t v_stop_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_eq(v_i_1317_, v_stop_1318_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_array_uget_borrowed(v_as_1316_, v_i_1317_);
v___x_1324_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1315_, v___x_1323_, v___y_1320_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; size_t v___x_1326_; size_t v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_i_1317_, v___x_1326_);
v_i_1317_ = v___x_1327_;
v_b_1319_ = v_a_1325_;
goto _start;
}
else
{
return v___x_1324_;
}
}
else
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_b_1319_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1330_, lean_object* v_as_1331_, lean_object* v_i_1332_, lean_object* v_stop_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v_pu_boxed_1337_; size_t v_i_boxed_1338_; size_t v_stop_boxed_1339_; lean_object* v_res_1340_; 
v_pu_boxed_1337_ = lean_unbox(v_pu_1330_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_stop_boxed_1339_ = lean_unbox_usize(v_stop_1333_);
lean_dec(v_stop_1333_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1337_, v_as_1331_, v_i_boxed_1338_, v_stop_boxed_1339_, v_b_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v_as_1331_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1341_, lean_object* v_decls_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_array_get_size(v_decls_1342_);
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_nat_dec_lt(v___x_1348_, v___x_1349_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
return v___x_1352_;
}
else
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_le(v___x_1349_, v___x_1349_);
if (v___x_1353_ == 0)
{
if (v___x_1351_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1350_);
return v___x_1354_;
}
else
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_of_nat(v___x_1349_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1341_, v_decls_1342_, v___x_1355_, v___x_1356_, v___x_1350_, v_a_1344_);
return v___x_1357_;
}
}
else
{
size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = lean_usize_of_nat(v___x_1349_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1341_, v_decls_1342_, v___x_1358_, v___x_1359_, v___x_1350_, v_a_1344_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1361_, lean_object* v_decls_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
uint8_t v_pu_boxed_1368_; lean_object* v_res_1369_; 
v_pu_boxed_1368_ = lean_unbox(v_pu_1361_);
v_res_1369_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1368_, v_decls_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec_ref(v_decls_1362_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1370_, lean_object* v_as_1371_, size_t v_i_1372_, size_t v_stop_1373_, lean_object* v_b_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1370_, v_as_1371_, v_i_1372_, v_stop_1373_, v_b_1374_, v___y_1376_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1381_, lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_stop_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_pu_boxed_1391_; size_t v_i_boxed_1392_; size_t v_stop_boxed_1393_; lean_object* v_res_1394_; 
v_pu_boxed_1391_ = lean_unbox(v_pu_1381_);
v_i_boxed_1392_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_stop_boxed_1393_ = lean_unbox_usize(v_stop_1384_);
lean_dec(v_stop_1384_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1391_, v_as_1382_, v_i_boxed_1392_, v_stop_boxed_1393_, v_b_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec_ref(v_as_1382_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1395_, lean_object* v_v_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
if (lean_obj_tag(v_v_1396_) == 0)
{
lean_object* v_code_1402_; lean_object* v___x_1403_; 
v_code_1402_ = lean_ctor_get(v_v_1396_, 0);
lean_inc_ref(v_code_1402_);
lean_dec_ref_known(v_v_1396_, 1);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
v___x_1403_ = lean_apply_6(v_f_1395_, v_code_1402_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, lean_box(0));
return v___x_1403_;
}
else
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_f_1395_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_v_1396_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_v_1396_, 0);
lean_dec(v_unused_1412_);
v___x_1405_ = v_v_1396_;
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_v_1396_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_box(0);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1407_);
v___x_1409_ = v___x_1405_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1413_, lean_object* v_v_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1413_, v_v_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1421_, lean_object* v_f_1422_, lean_object* v_v_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1422_, v_v_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1430_, lean_object* v_f_1431_, lean_object* v_v_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v_pu_boxed_1438_; lean_object* v_res_1439_; 
v_pu_boxed_1438_ = lean_unbox(v_pu_1430_);
v_res_1439_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1438_, v_f_1431_, v_v_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1440_, lean_object* v_decl_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_toSignature_1447_; lean_object* v_value_1448_; lean_object* v_params_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_toSignature_1447_ = lean_ctor_get(v_decl_1441_, 0);
lean_inc_ref(v_toSignature_1447_);
v_value_1448_ = lean_ctor_get(v_decl_1441_, 1);
lean_inc_ref(v_value_1448_);
lean_dec_ref(v_decl_1441_);
v_params_1449_ = lean_ctor_get(v_toSignature_1447_, 3);
lean_inc_ref(v_params_1449_);
lean_dec_ref(v_toSignature_1447_);
v___x_1450_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1440_, v_params_1449_, v_a_1443_);
lean_dec_ref(v_params_1449_);
lean_dec_ref(v___x_1450_);
v___x_1451_ = lean_box(v_pu_1440_);
v___x_1452_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1452_, 0, v___x_1451_);
v___x_1453_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1452_, v_value_1448_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1454_, lean_object* v_decl_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
uint8_t v_pu_boxed_1461_; lean_object* v_res_1462_; 
v_pu_boxed_1461_ = lean_unbox(v_pu_1454_);
v_res_1462_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1461_, v_decl_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1463_, lean_object* v_decl_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1463_, v_decl_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1471_, lean_object* v_decl_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
uint8_t v_pu_boxed_1478_; lean_object* v_res_1479_; 
v_pu_boxed_1478_ = lean_unbox(v_pu_1471_);
v_res_1479_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1478_, v_decl_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = l_Lean_instInhabitedExpr;
v___x_1482_ = lean_panic_fn_borrowed(v___x_1481_, v_msg_1480_);
return v___x_1482_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1487_ = lean_unsigned_to_nat(20u);
v___x_1488_ = lean_unsigned_to_nat(215u);
v___x_1489_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1490_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1491_ = l_mkPanicMessageWithDecl(v___x_1490_, v___x_1489_, v___x_1488_, v___x_1487_, v___x_1486_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1492_, lean_object* v_s_1493_, uint8_t v_translator_1494_, lean_object* v_e_1495_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = l_Lean_Expr_hasFVar(v_e_1495_);
if (v___x_1496_ == 0)
{
return v_e_1495_;
}
else
{
switch(lean_obj_tag(v_e_1495_))
{
case 1:
{
lean_object* v_fvarId_1497_; lean_object* v___x_1498_; 
v_fvarId_1497_ = lean_ctor_get(v_e_1495_, 0);
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1493_, v_fvarId_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
return v_e_1495_;
}
else
{
lean_object* v_val_1499_; 
lean_dec_ref_known(v_e_1495_, 1);
v_val_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v___x_1498_, 1);
switch(lean_obj_tag(v_val_1499_))
{
case 0:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1500_;
}
case 1:
{
if (v_translator_1494_ == 0)
{
lean_object* v_fvarId_1501_; lean_object* v___x_1502_; 
v_fvarId_1501_ = lean_ctor_get(v_val_1499_, 0);
lean_inc(v_fvarId_1501_);
lean_dec_ref_known(v_val_1499_, 1);
v___x_1502_ = l_Lean_Expr_fvar___override(v_fvarId_1501_);
v_e_1495_ = v___x_1502_;
goto _start;
}
else
{
lean_object* v_fvarId_1504_; lean_object* v___x_1505_; 
v_fvarId_1504_ = lean_ctor_get(v_val_1499_, 0);
lean_inc(v_fvarId_1504_);
lean_dec_ref_known(v_val_1499_, 1);
v___x_1505_ = l_Lean_Expr_fvar___override(v_fvarId_1504_);
return v___x_1505_;
}
}
default: 
{
if (v_translator_1494_ == 0)
{
lean_object* v_expr_1506_; 
v_expr_1506_ = lean_ctor_get(v_val_1499_, 0);
lean_inc_ref(v_expr_1506_);
lean_dec_ref_known(v_val_1499_, 1);
v_e_1495_ = v_expr_1506_;
goto _start;
}
else
{
lean_object* v_expr_1508_; 
v_expr_1508_ = lean_ctor_get(v_val_1499_, 0);
lean_inc_ref(v_expr_1508_);
lean_dec_ref_known(v_val_1499_, 1);
return v_expr_1508_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1509_; lean_object* v_arg_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v_fn_1509_ = lean_ctor_get(v_e_1495_, 0);
v_arg_1510_ = lean_ctor_get(v_e_1495_, 1);
lean_inc_ref(v_fn_1509_);
v___x_1511_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1492_, v_s_1493_, v_translator_1494_, v_fn_1509_);
lean_inc_ref(v_arg_1510_);
v___x_1512_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_arg_1510_);
v___x_1513_ = lean_ptr_addr(v_fn_1509_);
v___x_1514_ = lean_ptr_addr(v___x_1511_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref_known(v_e_1495_, 2);
v___x_1516_ = l_Lean_Expr_app___override(v___x_1511_, v___x_1512_);
v___x_1517_ = l_Lean_Expr_headBeta(v___x_1516_);
return v___x_1517_;
}
else
{
size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_ptr_addr(v_arg_1510_);
v___x_1519_ = lean_ptr_addr(v___x_1512_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref_known(v_e_1495_, 2);
v___x_1521_ = l_Lean_Expr_app___override(v___x_1511_, v___x_1512_);
v___x_1522_ = l_Lean_Expr_headBeta(v___x_1521_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref(v___x_1512_);
lean_dec_ref(v___x_1511_);
v___x_1523_ = l_Lean_Expr_headBeta(v_e_1495_);
return v___x_1523_;
}
}
}
case 6:
{
lean_object* v_binderName_1524_; lean_object* v_binderType_1525_; lean_object* v_body_1526_; uint8_t v_binderInfo_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; uint8_t v___x_1532_; 
v_binderName_1524_ = lean_ctor_get(v_e_1495_, 0);
v_binderType_1525_ = lean_ctor_get(v_e_1495_, 1);
v_body_1526_ = lean_ctor_get(v_e_1495_, 2);
v_binderInfo_1527_ = lean_ctor_get_uint8(v_e_1495_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1525_);
v___x_1528_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_binderType_1525_);
lean_inc_ref(v_body_1526_);
v___x_1529_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_body_1526_);
v___x_1530_ = lean_ptr_addr(v_binderType_1525_);
v___x_1531_ = lean_ptr_addr(v___x_1528_);
v___x_1532_ = lean_usize_dec_eq(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_inc(v_binderName_1524_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1533_ = l_Lean_Expr_lam___override(v_binderName_1524_, v___x_1528_, v___x_1529_, v_binderInfo_1527_);
return v___x_1533_;
}
else
{
size_t v___x_1534_; size_t v___x_1535_; uint8_t v___x_1536_; 
v___x_1534_ = lean_ptr_addr(v_body_1526_);
v___x_1535_ = lean_ptr_addr(v___x_1529_);
v___x_1536_ = lean_usize_dec_eq(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_inc(v_binderName_1524_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1537_ = l_Lean_Expr_lam___override(v_binderName_1524_, v___x_1528_, v___x_1529_, v_binderInfo_1527_);
return v___x_1537_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1527_, v_binderInfo_1527_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_inc(v_binderName_1524_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1539_ = l_Lean_Expr_lam___override(v_binderName_1524_, v___x_1528_, v___x_1529_, v_binderInfo_1527_);
return v___x_1539_;
}
else
{
lean_dec_ref(v___x_1529_);
lean_dec_ref(v___x_1528_);
return v_e_1495_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1540_; lean_object* v_binderType_1541_; lean_object* v_body_1542_; uint8_t v_binderInfo_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; uint8_t v___x_1548_; 
v_binderName_1540_ = lean_ctor_get(v_e_1495_, 0);
v_binderType_1541_ = lean_ctor_get(v_e_1495_, 1);
v_body_1542_ = lean_ctor_get(v_e_1495_, 2);
v_binderInfo_1543_ = lean_ctor_get_uint8(v_e_1495_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1541_);
v___x_1544_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_binderType_1541_);
lean_inc_ref(v_body_1542_);
v___x_1545_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_body_1542_);
v___x_1546_ = lean_ptr_addr(v_binderType_1541_);
v___x_1547_ = lean_ptr_addr(v___x_1544_);
v___x_1548_ = lean_usize_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_binderName_1540_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1549_ = l_Lean_Expr_forallE___override(v_binderName_1540_, v___x_1544_, v___x_1545_, v_binderInfo_1543_);
return v___x_1549_;
}
else
{
size_t v___x_1550_; size_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = lean_ptr_addr(v_body_1542_);
v___x_1551_ = lean_ptr_addr(v___x_1545_);
v___x_1552_ = lean_usize_dec_eq(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_inc(v_binderName_1540_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1553_ = l_Lean_Expr_forallE___override(v_binderName_1540_, v___x_1544_, v___x_1545_, v_binderInfo_1543_);
return v___x_1553_;
}
else
{
uint8_t v___x_1554_; 
v___x_1554_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1543_, v_binderInfo_1543_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_inc(v_binderName_1540_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1555_ = l_Lean_Expr_forallE___override(v_binderName_1540_, v___x_1544_, v___x_1545_, v_binderInfo_1543_);
return v___x_1555_;
}
else
{
lean_dec_ref(v___x_1545_);
lean_dec_ref(v___x_1544_);
return v_e_1495_;
}
}
}
}
case 8:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref_known(v_e_1495_, 4);
v___x_1556_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1557_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1556_);
return v___x_1557_;
}
case 10:
{
lean_object* v_data_1558_; lean_object* v_expr_1559_; lean_object* v___x_1560_; size_t v___x_1561_; size_t v___x_1562_; uint8_t v___x_1563_; 
v_data_1558_ = lean_ctor_get(v_e_1495_, 0);
v_expr_1559_ = lean_ctor_get(v_e_1495_, 1);
lean_inc_ref(v_expr_1559_);
v___x_1560_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_expr_1559_);
v___x_1561_ = lean_ptr_addr(v_expr_1559_);
v___x_1562_ = lean_ptr_addr(v___x_1560_);
v___x_1563_ = lean_usize_dec_eq(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_inc(v_data_1558_);
lean_dec_ref_known(v_e_1495_, 2);
v___x_1564_ = l_Lean_Expr_mdata___override(v_data_1558_, v___x_1560_);
return v___x_1564_;
}
else
{
lean_dec_ref(v___x_1560_);
return v_e_1495_;
}
}
case 11:
{
lean_object* v_typeName_1565_; lean_object* v_idx_1566_; lean_object* v_struct_1567_; lean_object* v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; uint8_t v___x_1571_; 
v_typeName_1565_ = lean_ctor_get(v_e_1495_, 0);
v_idx_1566_ = lean_ctor_get(v_e_1495_, 1);
v_struct_1567_ = lean_ctor_get(v_e_1495_, 2);
lean_inc_ref(v_struct_1567_);
v___x_1568_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1492_, v_s_1493_, v_translator_1494_, v_struct_1567_);
v___x_1569_ = lean_ptr_addr(v_struct_1567_);
v___x_1570_ = lean_ptr_addr(v___x_1568_);
v___x_1571_ = lean_usize_dec_eq(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_inc(v_idx_1566_);
lean_inc(v_typeName_1565_);
lean_dec_ref_known(v_e_1495_, 3);
v___x_1572_ = l_Lean_Expr_proj___override(v_typeName_1565_, v_idx_1566_, v___x_1568_);
return v___x_1572_;
}
else
{
lean_dec_ref(v___x_1568_);
return v_e_1495_;
}
}
default: 
{
return v_e_1495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1573_, lean_object* v_s_1574_, uint8_t v_translator_1575_, lean_object* v_e_1576_){
_start:
{
if (lean_obj_tag(v_e_1576_) == 5)
{
lean_object* v_fn_1577_; lean_object* v_arg_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; uint8_t v___x_1583_; 
v_fn_1577_ = lean_ctor_get(v_e_1576_, 0);
v_arg_1578_ = lean_ctor_get(v_e_1576_, 1);
lean_inc_ref(v_fn_1577_);
v___x_1579_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1573_, v_s_1574_, v_translator_1575_, v_fn_1577_);
lean_inc_ref(v_arg_1578_);
v___x_1580_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1573_, v_s_1574_, v_translator_1575_, v_arg_1578_);
v___x_1581_ = lean_ptr_addr(v_fn_1577_);
v___x_1582_ = lean_ptr_addr(v___x_1579_);
v___x_1583_ = lean_usize_dec_eq(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref_known(v_e_1576_, 2);
v___x_1584_ = l_Lean_Expr_app___override(v___x_1579_, v___x_1580_);
return v___x_1584_;
}
else
{
size_t v___x_1585_; size_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_ptr_addr(v_arg_1578_);
v___x_1586_ = lean_ptr_addr(v___x_1580_);
v___x_1587_ = lean_usize_dec_eq(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref_known(v_e_1576_, 2);
v___x_1588_ = l_Lean_Expr_app___override(v___x_1579_, v___x_1580_);
return v___x_1588_;
}
else
{
lean_dec_ref(v___x_1580_);
lean_dec_ref(v___x_1579_);
return v_e_1576_;
}
}
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1573_, v_s_1574_, v_translator_1575_, v_e_1576_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1590_, lean_object* v_s_1591_, lean_object* v_translator_1592_, lean_object* v_e_1593_){
_start:
{
uint8_t v_pu_boxed_1594_; uint8_t v_translator_boxed_1595_; lean_object* v_res_1596_; 
v_pu_boxed_1594_ = lean_unbox(v_pu_1590_);
v_translator_boxed_1595_ = lean_unbox(v_translator_1592_);
v_res_1596_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1594_, v_s_1591_, v_translator_boxed_1595_, v_e_1593_);
lean_dec_ref(v_s_1591_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1597_, lean_object* v_s_1598_, lean_object* v_translator_1599_, lean_object* v_e_1600_){
_start:
{
uint8_t v_pu_boxed_1601_; uint8_t v_translator_boxed_1602_; lean_object* v_res_1603_; 
v_pu_boxed_1601_ = lean_unbox(v_pu_1597_);
v_translator_boxed_1602_ = lean_unbox(v_translator_1599_);
v_res_1603_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1601_, v_s_1598_, v_translator_boxed_1602_, v_e_1600_);
lean_dec_ref(v_s_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1604_, lean_object* v_s_1605_, lean_object* v_e_1606_, uint8_t v_translator_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1604_, v_s_1605_, v_translator_1607_, v_e_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1609_, lean_object* v_s_1610_, lean_object* v_e_1611_, lean_object* v_translator_1612_){
_start:
{
uint8_t v_pu_boxed_1613_; uint8_t v_translator_boxed_1614_; lean_object* v_res_1615_; 
v_pu_boxed_1613_ = lean_unbox(v_pu_1609_);
v_translator_boxed_1614_ = lean_unbox(v_translator_1612_);
v_res_1615_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1613_, v_s_1610_, v_e_1611_, v_translator_boxed_1614_);
lean_dec_ref(v_s_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_unsigned_to_nat(1u);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1619_);
lean_dec(v_x_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1621_, lean_object* v_k_1622_){
_start:
{
if (lean_obj_tag(v_t_1621_) == 0)
{
lean_object* v_fvarId_1623_; lean_object* v___x_1624_; 
v_fvarId_1623_ = lean_ctor_get(v_t_1621_, 0);
lean_inc(v_fvarId_1623_);
lean_dec_ref_known(v_t_1621_, 1);
v___x_1624_ = lean_apply_1(v_k_1622_, v_fvarId_1623_);
return v___x_1624_;
}
else
{
return v_k_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1625_, lean_object* v_ctorIdx_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_k_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1627_, v_k_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1631_, lean_object* v_ctorIdx_1632_, lean_object* v_t_1633_, lean_object* v_h_1634_, lean_object* v_k_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1631_, v_ctorIdx_1632_, v_t_1633_, v_h_1634_, v_k_1635_);
lean_dec(v_ctorIdx_1632_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1637_, lean_object* v_fvar_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1637_, v_fvar_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1640_, lean_object* v_t_1641_, lean_object* v_h_1642_, lean_object* v_fvar_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1641_, v_fvar_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1645_, lean_object* v_erased_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1645_, v_erased_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1648_, lean_object* v_t_1649_, lean_object* v_h_1650_, lean_object* v_erased_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1649_, v_erased_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1657_, lean_object* v_fvarId_1658_, uint8_t v_translator_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1657_, v_fvarId_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_fvarId_1658_);
return v___x_1661_;
}
else
{
lean_object* v_val_1662_; 
lean_dec(v_fvarId_1658_);
v_val_1662_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v___x_1660_, 1);
if (lean_obj_tag(v_val_1662_) == 1)
{
if (v_translator_1659_ == 0)
{
lean_object* v_fvarId_1663_; 
v_fvarId_1663_ = lean_ctor_get(v_val_1662_, 0);
lean_inc(v_fvarId_1663_);
lean_dec_ref_known(v_val_1662_, 1);
v_fvarId_1658_ = v_fvarId_1663_;
goto _start;
}
else
{
lean_object* v_fvarId_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_fvarId_1665_ = lean_ctor_get(v_val_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_val_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v_val_1662_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_fvarId_1665_);
lean_dec(v_val_1662_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 0);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_fvarId_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v___x_1673_; 
lean_dec(v_val_1662_);
v___x_1673_ = lean_box(1);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1674_, lean_object* v_fvarId_1675_, lean_object* v_translator_1676_){
_start:
{
uint8_t v_translator_boxed_1677_; lean_object* v_res_1678_; 
v_translator_boxed_1677_ = lean_unbox(v_translator_1676_);
v_res_1678_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1674_, v_fvarId_1675_, v_translator_boxed_1677_);
lean_dec_ref(v_s_1674_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1679_, lean_object* v_s_1680_, lean_object* v_fvarId_1681_, uint8_t v_translator_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1680_, v_fvarId_1681_, v_translator_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1684_, lean_object* v_s_1685_, lean_object* v_fvarId_1686_, lean_object* v_translator_1687_){
_start:
{
uint8_t v_pu_boxed_1688_; uint8_t v_translator_boxed_1689_; lean_object* v_res_1690_; 
v_pu_boxed_1688_ = lean_unbox(v_pu_1684_);
v_translator_boxed_1689_ = lean_unbox(v_translator_1687_);
v_res_1690_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1688_, v_s_1685_, v_fvarId_1686_, v_translator_boxed_1689_);
lean_dec_ref(v_s_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1691_, lean_object* v_s_1692_, lean_object* v_arg_1693_, uint8_t v_translator_1694_){
_start:
{
switch(lean_obj_tag(v_arg_1693_))
{
case 0:
{
return v_arg_1693_;
}
case 1:
{
lean_object* v_fvarId_1695_; lean_object* v___x_1696_; 
v_fvarId_1695_ = lean_ctor_get(v_arg_1693_, 0);
v___x_1696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1692_, v_fvarId_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
return v_arg_1693_;
}
else
{
lean_object* v_val_1697_; 
lean_dec_ref_known(v_arg_1693_, 1);
v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___x_1696_, 1);
switch(lean_obj_tag(v_val_1697_))
{
case 0:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_box(0);
return v___x_1698_;
}
case 1:
{
lean_object* v_fvarId_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_fvarId_1699_ = lean_ctor_get(v_val_1697_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_val_1697_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v_val_1697_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_fvarId_1699_);
lean_dec(v_val_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_fvarId_1699_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
if (v_translator_1694_ == 0)
{
v_arg_1693_ = v___x_1704_;
goto _start;
}
else
{
return v___x_1704_;
}
}
}
}
default: 
{
lean_object* v_expr_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_expr_1708_ = lean_ctor_get(v_val_1697_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_val_1697_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v_val_1697_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_expr_1708_);
lean_dec(v_val_1697_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_expr_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_expr_1716_ = lean_ctor_get(v_arg_1693_, 0);
lean_inc_ref(v_expr_1716_);
v___x_1717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1691_, v_s_1692_, v_translator_1694_, v_expr_1716_);
v___x_1718_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1691_, v_arg_1693_, v___x_1717_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1719_, lean_object* v_s_1720_, lean_object* v_arg_1721_, lean_object* v_translator_1722_){
_start:
{
uint8_t v_pu_boxed_1723_; uint8_t v_translator_boxed_1724_; lean_object* v_res_1725_; 
v_pu_boxed_1723_ = lean_unbox(v_pu_1719_);
v_translator_boxed_1724_ = lean_unbox(v_translator_1722_);
v_res_1725_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1723_, v_s_1720_, v_arg_1721_, v_translator_boxed_1724_);
lean_dec_ref(v_s_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1726_, lean_object* v_s_1727_, uint8_t v_translator_1728_, lean_object* v_i_1729_, lean_object* v_as_1730_){
_start:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = lean_array_get_size(v_as_1730_);
v___x_1732_ = lean_nat_dec_lt(v_i_1729_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_dec(v_i_1729_);
return v_as_1730_;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; uint8_t v___x_1737_; 
v_a_1733_ = lean_array_fget_borrowed(v_as_1730_, v_i_1729_);
lean_inc(v_a_1733_);
v___x_1734_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1726_, v_s_1727_, v_a_1733_, v_translator_1728_);
v___x_1735_ = lean_ptr_addr(v_a_1733_);
v___x_1736_ = lean_ptr_addr(v___x_1734_);
v___x_1737_ = lean_usize_dec_eq(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1729_, v___x_1738_);
v___x_1740_ = lean_array_fset(v_as_1730_, v_i_1729_, v___x_1734_);
lean_dec(v_i_1729_);
v_i_1729_ = v___x_1739_;
v_as_1730_ = v___x_1740_;
goto _start;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v___x_1734_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_i_1729_, v___x_1742_);
lean_dec(v_i_1729_);
v_i_1729_ = v___x_1743_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1745_, lean_object* v_s_1746_, lean_object* v_translator_1747_, lean_object* v_i_1748_, lean_object* v_as_1749_){
_start:
{
uint8_t v_pu_boxed_1750_; uint8_t v_translator_boxed_1751_; lean_object* v_res_1752_; 
v_pu_boxed_1750_ = lean_unbox(v_pu_1745_);
v_translator_boxed_1751_ = lean_unbox(v_translator_1747_);
v_res_1752_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1750_, v_s_1746_, v_translator_boxed_1751_, v_i_1748_, v_as_1749_);
lean_dec_ref(v_s_1746_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1753_, lean_object* v_s_1754_, lean_object* v_args_1755_, uint8_t v_translator_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1753_, v_s_1754_, v_translator_1756_, v___x_1757_, v_args_1755_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1759_, lean_object* v_s_1760_, lean_object* v_args_1761_, lean_object* v_translator_1762_){
_start:
{
uint8_t v_pu_boxed_1763_; uint8_t v_translator_boxed_1764_; lean_object* v_res_1765_; 
v_pu_boxed_1763_ = lean_unbox(v_pu_1759_);
v_translator_boxed_1764_ = lean_unbox(v_translator_1762_);
v_res_1765_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1763_, v_s_1760_, v_args_1761_, v_translator_boxed_1764_);
lean_dec_ref(v_s_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1766_, lean_object* v_s_1767_, lean_object* v_e_1768_, uint8_t v_translator_1769_){
_start:
{
lean_object* v_fvarId_1771_; lean_object* v_args_1777_; 
switch(lean_obj_tag(v_e_1768_))
{
case 2:
{
lean_object* v_struct_1780_; lean_object* v___x_1781_; 
v_struct_1780_ = lean_ctor_get(v_e_1768_, 2);
lean_inc(v_struct_1780_);
v___x_1781_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_struct_1780_, v_translator_1769_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_fvarId_1782_; lean_object* v___x_1783_; 
v_fvarId_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_fvarId_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1766_, v_e_1768_, v_fvarId_1782_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; 
lean_dec_ref_known(v_e_1768_, 3);
v___x_1784_ = lean_box(1);
return v___x_1784_;
}
}
case 3:
{
lean_object* v_args_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_args_1785_ = lean_ctor_get(v_e_1768_, 2);
lean_inc_ref(v_args_1785_);
v___x_1786_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1785_, v_translator_1769_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1768_, v___x_1786_);
return v___x_1787_;
}
case 4:
{
lean_object* v_fvarId_1788_; lean_object* v_args_1789_; lean_object* v___x_1790_; 
v_fvarId_1788_ = lean_ctor_get(v_e_1768_, 0);
v_args_1789_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_fvarId_1788_);
v___x_1790_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1788_, v_translator_1769_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_fvarId_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_fvarId_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_fvarId_1791_);
lean_dec_ref_known(v___x_1790_, 1);
lean_inc_ref(v_args_1789_);
v___x_1792_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1789_, v_translator_1769_);
v___x_1793_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1768_, v_fvarId_1791_, v___x_1792_);
lean_dec_ref_known(v_e_1768_, 2);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; 
lean_dec_ref_known(v_e_1768_, 2);
v___x_1794_ = lean_box(1);
return v___x_1794_;
}
}
case 5:
{
lean_object* v_args_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_args_1795_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_args_1795_);
v___x_1796_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1795_, v_translator_1769_);
v___x_1797_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1768_, v___x_1796_);
return v___x_1797_;
}
case 6:
{
lean_object* v_var_1798_; 
v_var_1798_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_var_1798_);
v_fvarId_1771_ = v_var_1798_;
goto v___jp_1770_;
}
case 7:
{
lean_object* v_var_1799_; 
v_var_1799_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_var_1799_);
v_fvarId_1771_ = v_var_1799_;
goto v___jp_1770_;
}
case 8:
{
lean_object* v_var_1800_; lean_object* v___x_1801_; 
v_var_1800_ = lean_ctor_get(v_e_1768_, 2);
lean_inc(v_var_1800_);
v___x_1801_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_var_1800_, v_translator_1769_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_fvarId_1802_; lean_object* v___x_1803_; 
v_fvarId_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_fvarId_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1766_, v_e_1768_, v_fvarId_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v_e_1768_, 3);
v___x_1804_ = lean_box(1);
return v___x_1804_;
}
}
case 9:
{
lean_object* v_args_1805_; 
v_args_1805_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_args_1805_);
v_args_1777_ = v_args_1805_;
goto v___jp_1776_;
}
case 10:
{
lean_object* v_args_1806_; 
v_args_1806_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_args_1806_);
v_args_1777_ = v_args_1806_;
goto v___jp_1776_;
}
case 11:
{
lean_object* v_n_1807_; lean_object* v_var_1808_; lean_object* v___x_1809_; 
v_n_1807_ = lean_ctor_get(v_e_1768_, 0);
lean_inc(v_n_1807_);
v_var_1808_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_var_1808_);
v___x_1809_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_var_1808_, v_translator_1769_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_fvarId_1810_; lean_object* v___x_1811_; 
v_fvarId_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_fvarId_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1768_, v_n_1807_, v_fvarId_1810_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; 
lean_dec_ref_known(v_e_1768_, 2);
lean_dec(v_n_1807_);
v___x_1812_ = lean_box(1);
return v___x_1812_;
}
}
case 12:
{
lean_object* v_var_1813_; lean_object* v_i_1814_; uint8_t v_updateHeader_1815_; lean_object* v_args_1816_; lean_object* v___x_1817_; 
v_var_1813_ = lean_ctor_get(v_e_1768_, 0);
v_i_1814_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_i_1814_);
v_updateHeader_1815_ = lean_ctor_get_uint8(v_e_1768_, sizeof(void*)*3);
v_args_1816_ = lean_ctor_get(v_e_1768_, 2);
lean_inc(v_var_1813_);
v___x_1817_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_var_1813_, v_translator_1769_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_fvarId_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_fvarId_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_fvarId_1818_);
lean_dec_ref_known(v___x_1817_, 1);
lean_inc_ref(v_args_1816_);
v___x_1819_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1816_, v_translator_1769_);
v___x_1820_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1768_, v_fvarId_1818_, v_i_1814_, v_updateHeader_1815_, v___x_1819_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v_i_1814_);
lean_dec_ref_known(v_e_1768_, 3);
v___x_1821_ = lean_box(1);
return v___x_1821_;
}
}
case 13:
{
lean_object* v_ty_1822_; lean_object* v_fvarId_1823_; lean_object* v___x_1824_; 
v_ty_1822_ = lean_ctor_get(v_e_1768_, 0);
lean_inc_ref(v_ty_1822_);
v_fvarId_1823_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_fvarId_1823_);
v___x_1824_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1823_, v_translator_1769_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_fvarId_1825_; lean_object* v___x_1826_; 
v_fvarId_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_fvarId_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1768_, v_ty_1822_, v_fvarId_1825_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref_known(v_e_1768_, 2);
lean_dec_ref(v_ty_1822_);
v___x_1827_ = lean_box(1);
return v___x_1827_;
}
}
case 14:
{
lean_object* v_fvarId_1828_; lean_object* v___x_1829_; 
v_fvarId_1828_ = lean_ctor_get(v_e_1768_, 0);
lean_inc(v_fvarId_1828_);
v___x_1829_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1828_, v_translator_1769_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_fvarId_1830_; lean_object* v___x_1831_; 
v_fvarId_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_fvarId_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1768_, v_fvarId_1830_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; 
lean_dec_ref_known(v_e_1768_, 1);
v___x_1832_ = lean_box(1);
return v___x_1832_;
}
}
case 15:
{
lean_object* v_fvarId_1833_; lean_object* v___x_1834_; 
v_fvarId_1833_ = lean_ctor_get(v_e_1768_, 0);
lean_inc(v_fvarId_1833_);
v___x_1834_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1833_, v_translator_1769_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_fvarId_1835_; lean_object* v___x_1836_; 
v_fvarId_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_fvarId_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1768_, v_fvarId_1835_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; 
lean_dec_ref_known(v_e_1768_, 1);
v___x_1837_ = lean_box(1);
return v___x_1837_;
}
}
default: 
{
return v_e_1768_;
}
}
v___jp_1770_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1771_, v_translator_1769_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_fvarId_1773_; lean_object* v___x_1774_; 
v_fvarId_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_fvarId_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1766_, v_e_1768_, v_fvarId_1773_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_e_1768_);
v___x_1775_ = lean_box(1);
return v___x_1775_;
}
}
v___jp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1777_, v_translator_1769_);
v___x_1779_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1768_, v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1838_, lean_object* v_s_1839_, lean_object* v_e_1840_, lean_object* v_translator_1841_){
_start:
{
uint8_t v_pu_boxed_1842_; uint8_t v_translator_boxed_1843_; lean_object* v_res_1844_; 
v_pu_boxed_1842_ = lean_unbox(v_pu_1838_);
v_translator_boxed_1843_ = lean_unbox(v_translator_1841_);
v_res_1844_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1842_, v_s_1839_, v_e_1840_, v_translator_boxed_1843_);
lean_dec_ref(v_s_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1845_, lean_object* v_inst_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_apply_2(v_inst_1845_, lean_box(0), v_inst_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1848_, uint8_t v_t_1849_, lean_object* v_m_1850_, lean_object* v_n_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_apply_2(v_inst_1852_, lean_box(0), v_inst_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1855_, lean_object* v_t_1856_, lean_object* v_m_1857_, lean_object* v_n_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_){
_start:
{
uint8_t v_pu_boxed_1861_; uint8_t v_t_boxed_1862_; lean_object* v_res_1863_; 
v_pu_boxed_1861_ = lean_unbox(v_pu_1855_);
v_t_boxed_1862_ = lean_unbox(v_t_1856_);
v_res_1863_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1861_, v_t_boxed_1862_, v_m_1857_, v_n_1858_, v_inst_1859_, v_inst_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_f_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_apply_1(v_inst_1864_, v_f_1866_);
v___x_1868_ = lean_apply_2(v_inst_1865_, lean_box(0), v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1869_, lean_object* v_inst_1870_){
_start:
{
lean_object* v___f_1871_; 
v___f_1871_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1871_, 0, v_inst_1870_);
lean_closure_set(v___f_1871_, 1, v_inst_1869_);
return v___f_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1872_, lean_object* v_m_1873_, lean_object* v_n_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_){
_start:
{
lean_object* v___f_1877_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1877_, 0, v_inst_1876_);
lean_closure_set(v___f_1877_, 1, v_inst_1875_);
return v___f_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1878_, lean_object* v_m_1879_, lean_object* v_n_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_){
_start:
{
uint8_t v_pu_boxed_1883_; lean_object* v_res_1884_; 
v_pu_boxed_1883_ = lean_unbox(v_pu_1878_);
v_res_1884_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1883_, v_m_1879_, v_n_1880_, v_inst_1881_, v_inst_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1885_, lean_object* v___x_1886_, lean_object* v_fvarId_1887_, lean_object* v_arg_1888_, lean_object* v_s_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1885_, v___x_1886_, v_s_1889_, v_fvarId_1887_, v_arg_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1893_, lean_object* v_fvarId_1894_, lean_object* v_arg_1895_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
v___x_1896_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1897_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1898_, 0, v___x_1896_);
lean_closure_set(v___f_1898_, 1, v___x_1897_);
lean_closure_set(v___f_1898_, 2, v_fvarId_1894_);
lean_closure_set(v___f_1898_, 3, v_arg_1895_);
v___x_1899_ = lean_apply_1(v_inst_1893_, v___f_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1900_, uint8_t v_pu_1901_, lean_object* v_inst_1902_, lean_object* v_fvarId_1903_, lean_object* v_arg_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; 
v___x_1905_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1906_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1907_, 0, v___x_1905_);
lean_closure_set(v___f_1907_, 1, v___x_1906_);
lean_closure_set(v___f_1907_, 2, v_fvarId_1903_);
lean_closure_set(v___f_1907_, 3, v_arg_1904_);
v___x_1908_ = lean_apply_1(v_inst_1902_, v___f_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1909_, lean_object* v_pu_1910_, lean_object* v_inst_1911_, lean_object* v_fvarId_1912_, lean_object* v_arg_1913_){
_start:
{
uint8_t v_pu_boxed_1914_; lean_object* v_res_1915_; 
v_pu_boxed_1914_ = lean_unbox(v_pu_1910_);
v_res_1915_ = l_Lean_Compiler_LCNF_addSubst(v_m_1909_, v_pu_boxed_1914_, v_inst_1911_, v_fvarId_1912_, v_arg_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1916_, lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v_fvarId_1919_, lean_object* v_s_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_fvarId_x27_1916_);
v___x_1922_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1917_, v___x_1918_, v_s_1920_, v_fvarId_1919_, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1923_, lean_object* v_fvarId_1924_, lean_object* v_fvarId_x27_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; 
v___x_1926_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1928_, 0, v_fvarId_x27_1925_);
lean_closure_set(v___f_1928_, 1, v___x_1926_);
lean_closure_set(v___f_1928_, 2, v___x_1927_);
lean_closure_set(v___f_1928_, 3, v_fvarId_1924_);
v___x_1929_ = lean_apply_1(v_inst_1923_, v___f_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1930_, uint8_t v_ph_1931_, lean_object* v_inst_1932_, lean_object* v_fvarId_1933_, lean_object* v_fvarId_x27_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___x_1935_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1936_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1937_, 0, v_fvarId_x27_1934_);
lean_closure_set(v___f_1937_, 1, v___x_1935_);
lean_closure_set(v___f_1937_, 2, v___x_1936_);
lean_closure_set(v___f_1937_, 3, v_fvarId_1933_);
v___x_1938_ = lean_apply_1(v_inst_1932_, v___f_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1939_, lean_object* v_ph_1940_, lean_object* v_inst_1941_, lean_object* v_fvarId_1942_, lean_object* v_fvarId_x27_1943_){
_start:
{
uint8_t v_ph_boxed_1944_; lean_object* v_res_1945_; 
v_ph_boxed_1944_ = lean_unbox(v_ph_1940_);
v_res_1945_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1939_, v_ph_boxed_1944_, v_inst_1941_, v_fvarId_1942_, v_fvarId_x27_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1946_, uint8_t v_t_1947_, lean_object* v_toPure_1948_, lean_object* v_____do__lift_1949_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1949_, v_fvarId_1946_, v_t_1947_);
v___x_1951_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1952_, lean_object* v_t_1953_, lean_object* v_toPure_1954_, lean_object* v_____do__lift_1955_){
_start:
{
uint8_t v_t_boxed_1956_; lean_object* v_res_1957_; 
v_t_boxed_1956_ = lean_unbox(v_t_1953_);
v_res_1957_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1952_, v_t_boxed_1956_, v_toPure_1954_, v_____do__lift_1955_);
lean_dec_ref(v_____do__lift_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_fvarId_1961_){
_start:
{
lean_object* v_toApplicative_1962_; lean_object* v_toBind_1963_; lean_object* v_toPure_1964_; lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; 
v_toApplicative_1962_ = lean_ctor_get(v_inst_1960_, 0);
lean_inc_ref(v_toApplicative_1962_);
v_toBind_1963_ = lean_ctor_get(v_inst_1960_, 1);
lean_inc(v_toBind_1963_);
lean_dec_ref(v_inst_1960_);
v_toPure_1964_ = lean_ctor_get(v_toApplicative_1962_, 1);
lean_inc(v_toPure_1964_);
lean_dec_ref(v_toApplicative_1962_);
v___x_1965_ = lean_box(v_t_1958_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1966_, 0, v_fvarId_1961_);
lean_closure_set(v___f_1966_, 1, v___x_1965_);
lean_closure_set(v___f_1966_, 2, v_toPure_1964_);
v___x_1967_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v_inst_1959_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_fvarId_1971_){
_start:
{
uint8_t v_t_boxed_1972_; lean_object* v_res_1973_; 
v_t_boxed_1972_ = lean_unbox(v_t_1968_);
v_res_1973_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1972_, v_inst_1969_, v_inst_1970_, v_fvarId_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1974_, uint8_t v_pu_1975_, uint8_t v_t_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_fvarId_1979_){
_start:
{
lean_object* v_toApplicative_1980_; lean_object* v_toBind_1981_; lean_object* v_toPure_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; 
v_toApplicative_1980_ = lean_ctor_get(v_inst_1978_, 0);
lean_inc_ref(v_toApplicative_1980_);
v_toBind_1981_ = lean_ctor_get(v_inst_1978_, 1);
lean_inc(v_toBind_1981_);
lean_dec_ref(v_inst_1978_);
v_toPure_1982_ = lean_ctor_get(v_toApplicative_1980_, 1);
lean_inc(v_toPure_1982_);
lean_dec_ref(v_toApplicative_1980_);
v___x_1983_ = lean_box(v_t_1976_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1984_, 0, v_fvarId_1979_);
lean_closure_set(v___f_1984_, 1, v___x_1983_);
lean_closure_set(v___f_1984_, 2, v_toPure_1982_);
v___x_1985_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v_inst_1977_, v___f_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1986_, lean_object* v_pu_1987_, lean_object* v_t_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_fvarId_1991_){
_start:
{
uint8_t v_pu_boxed_1992_; uint8_t v_t_boxed_1993_; lean_object* v_res_1994_; 
v_pu_boxed_1992_ = lean_unbox(v_pu_1987_);
v_t_boxed_1993_ = lean_unbox(v_t_1988_);
v_res_1994_ = l_Lean_Compiler_LCNF_normFVar(v_m_1986_, v_pu_boxed_1992_, v_t_boxed_1993_, v_inst_1989_, v_inst_1990_, v_fvarId_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1995_, uint8_t v_t_1996_, lean_object* v_e_1997_, lean_object* v_toPure_1998_, lean_object* v_____do__lift_1999_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1995_, v_____do__lift_1999_, v_t_1996_, v_e_1997_);
v___x_2001_ = lean_apply_2(v_toPure_1998_, lean_box(0), v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2002_, lean_object* v_t_2003_, lean_object* v_e_2004_, lean_object* v_toPure_2005_, lean_object* v_____do__lift_2006_){
_start:
{
uint8_t v_pu_boxed_2007_; uint8_t v_t_boxed_2008_; lean_object* v_res_2009_; 
v_pu_boxed_2007_ = lean_unbox(v_pu_2002_);
v_t_boxed_2008_ = lean_unbox(v_t_2003_);
v_res_2009_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2007_, v_t_boxed_2008_, v_e_2004_, v_toPure_2005_, v_____do__lift_2006_);
lean_dec_ref(v_____do__lift_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2010_, uint8_t v_t_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_e_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toBind_2016_; lean_object* v_toPure_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___f_2020_; lean_object* v___x_2021_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2013_, 0);
lean_inc_ref(v_toApplicative_2015_);
v_toBind_2016_ = lean_ctor_get(v_inst_2013_, 1);
lean_inc(v_toBind_2016_);
lean_dec_ref(v_inst_2013_);
v_toPure_2017_ = lean_ctor_get(v_toApplicative_2015_, 1);
lean_inc(v_toPure_2017_);
lean_dec_ref(v_toApplicative_2015_);
v___x_2018_ = lean_box(v_pu_2010_);
v___x_2019_ = lean_box(v_t_2011_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2020_, 0, v___x_2018_);
lean_closure_set(v___f_2020_, 1, v___x_2019_);
lean_closure_set(v___f_2020_, 2, v_e_2014_);
lean_closure_set(v___f_2020_, 3, v_toPure_2017_);
v___x_2021_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v_inst_2012_, v___f_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2022_, lean_object* v_t_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_e_2026_){
_start:
{
uint8_t v_pu_boxed_2027_; uint8_t v_t_boxed_2028_; lean_object* v_res_2029_; 
v_pu_boxed_2027_ = lean_unbox(v_pu_2022_);
v_t_boxed_2028_ = lean_unbox(v_t_2023_);
v_res_2029_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2027_, v_t_boxed_2028_, v_inst_2024_, v_inst_2025_, v_e_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2030_, uint8_t v_pu_2031_, uint8_t v_t_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_e_2035_){
_start:
{
lean_object* v_toApplicative_2036_; lean_object* v_toBind_2037_; lean_object* v_toPure_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; 
v_toApplicative_2036_ = lean_ctor_get(v_inst_2034_, 0);
lean_inc_ref(v_toApplicative_2036_);
v_toBind_2037_ = lean_ctor_get(v_inst_2034_, 1);
lean_inc(v_toBind_2037_);
lean_dec_ref(v_inst_2034_);
v_toPure_2038_ = lean_ctor_get(v_toApplicative_2036_, 1);
lean_inc(v_toPure_2038_);
lean_dec_ref(v_toApplicative_2036_);
v___x_2039_ = lean_box(v_pu_2031_);
v___x_2040_ = lean_box(v_t_2032_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2041_, 0, v___x_2039_);
lean_closure_set(v___f_2041_, 1, v___x_2040_);
lean_closure_set(v___f_2041_, 2, v_e_2035_);
lean_closure_set(v___f_2041_, 3, v_toPure_2038_);
v___x_2042_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v_inst_2033_, v___f_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2043_, lean_object* v_pu_2044_, lean_object* v_t_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_e_2048_){
_start:
{
uint8_t v_pu_boxed_2049_; uint8_t v_t_boxed_2050_; lean_object* v_res_2051_; 
v_pu_boxed_2049_ = lean_unbox(v_pu_2044_);
v_t_boxed_2050_ = lean_unbox(v_t_2045_);
v_res_2051_ = l_Lean_Compiler_LCNF_normExpr(v_m_2043_, v_pu_boxed_2049_, v_t_boxed_2050_, v_inst_2046_, v_inst_2047_, v_e_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2052_, lean_object* v_arg_2053_, uint8_t v_t_2054_, lean_object* v_toPure_2055_, lean_object* v_____do__lift_2056_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2052_, v_____do__lift_2056_, v_arg_2053_, v_t_2054_);
v___x_2058_ = lean_apply_2(v_toPure_2055_, lean_box(0), v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2059_, lean_object* v_arg_2060_, lean_object* v_t_2061_, lean_object* v_toPure_2062_, lean_object* v_____do__lift_2063_){
_start:
{
uint8_t v_pu_boxed_2064_; uint8_t v_t_boxed_2065_; lean_object* v_res_2066_; 
v_pu_boxed_2064_ = lean_unbox(v_pu_2059_);
v_t_boxed_2065_ = lean_unbox(v_t_2061_);
v_res_2066_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2064_, v_arg_2060_, v_t_boxed_2065_, v_toPure_2062_, v_____do__lift_2063_);
lean_dec_ref(v_____do__lift_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2067_, uint8_t v_t_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_arg_2071_){
_start:
{
lean_object* v_toApplicative_2072_; lean_object* v_toBind_2073_; lean_object* v_toPure_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2070_, 0);
lean_inc_ref(v_toApplicative_2072_);
v_toBind_2073_ = lean_ctor_get(v_inst_2070_, 1);
lean_inc(v_toBind_2073_);
lean_dec_ref(v_inst_2070_);
v_toPure_2074_ = lean_ctor_get(v_toApplicative_2072_, 1);
lean_inc(v_toPure_2074_);
lean_dec_ref(v_toApplicative_2072_);
v___x_2075_ = lean_box(v_pu_2067_);
v___x_2076_ = lean_box(v_t_2068_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2077_, 0, v___x_2075_);
lean_closure_set(v___f_2077_, 1, v_arg_2071_);
lean_closure_set(v___f_2077_, 2, v___x_2076_);
lean_closure_set(v___f_2077_, 3, v_toPure_2074_);
v___x_2078_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v_inst_2069_, v___f_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2079_, lean_object* v_t_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_arg_2083_){
_start:
{
uint8_t v_pu_boxed_2084_; uint8_t v_t_boxed_2085_; lean_object* v_res_2086_; 
v_pu_boxed_2084_ = lean_unbox(v_pu_2079_);
v_t_boxed_2085_ = lean_unbox(v_t_2080_);
v_res_2086_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2084_, v_t_boxed_2085_, v_inst_2081_, v_inst_2082_, v_arg_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2087_, uint8_t v_pu_2088_, uint8_t v_t_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_arg_2092_){
_start:
{
lean_object* v_toApplicative_2093_; lean_object* v_toBind_2094_; lean_object* v_toPure_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; 
v_toApplicative_2093_ = lean_ctor_get(v_inst_2091_, 0);
lean_inc_ref(v_toApplicative_2093_);
v_toBind_2094_ = lean_ctor_get(v_inst_2091_, 1);
lean_inc(v_toBind_2094_);
lean_dec_ref(v_inst_2091_);
v_toPure_2095_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2095_);
lean_dec_ref(v_toApplicative_2093_);
v___x_2096_ = lean_box(v_pu_2088_);
v___x_2097_ = lean_box(v_t_2089_);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2098_, 0, v___x_2096_);
lean_closure_set(v___f_2098_, 1, v_arg_2092_);
lean_closure_set(v___f_2098_, 2, v___x_2097_);
lean_closure_set(v___f_2098_, 3, v_toPure_2095_);
v___x_2099_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v_inst_2090_, v___f_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2100_, lean_object* v_pu_2101_, lean_object* v_t_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_arg_2105_){
_start:
{
uint8_t v_pu_boxed_2106_; uint8_t v_t_boxed_2107_; lean_object* v_res_2108_; 
v_pu_boxed_2106_ = lean_unbox(v_pu_2101_);
v_t_boxed_2107_ = lean_unbox(v_t_2102_);
v_res_2108_ = l_Lean_Compiler_LCNF_normArg(v_m_2100_, v_pu_boxed_2106_, v_t_boxed_2107_, v_inst_2103_, v_inst_2104_, v_arg_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2109_, lean_object* v_e_2110_, uint8_t v_t_2111_, lean_object* v_toPure_2112_, lean_object* v_____do__lift_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2109_, v_____do__lift_2113_, v_e_2110_, v_t_2111_);
v___x_2115_ = lean_apply_2(v_toPure_2112_, lean_box(0), v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2116_, lean_object* v_e_2117_, lean_object* v_t_2118_, lean_object* v_toPure_2119_, lean_object* v_____do__lift_2120_){
_start:
{
uint8_t v_pu_boxed_2121_; uint8_t v_t_boxed_2122_; lean_object* v_res_2123_; 
v_pu_boxed_2121_ = lean_unbox(v_pu_2116_);
v_t_boxed_2122_ = lean_unbox(v_t_2118_);
v_res_2123_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2121_, v_e_2117_, v_t_boxed_2122_, v_toPure_2119_, v_____do__lift_2120_);
lean_dec_ref(v_____do__lift_2120_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2124_, uint8_t v_t_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_e_2128_){
_start:
{
lean_object* v_toApplicative_2129_; lean_object* v_toBind_2130_; lean_object* v_toPure_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; 
v_toApplicative_2129_ = lean_ctor_get(v_inst_2127_, 0);
lean_inc_ref(v_toApplicative_2129_);
v_toBind_2130_ = lean_ctor_get(v_inst_2127_, 1);
lean_inc(v_toBind_2130_);
lean_dec_ref(v_inst_2127_);
v_toPure_2131_ = lean_ctor_get(v_toApplicative_2129_, 1);
lean_inc(v_toPure_2131_);
lean_dec_ref(v_toApplicative_2129_);
v___x_2132_ = lean_box(v_pu_2124_);
v___x_2133_ = lean_box(v_t_2125_);
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2134_, 0, v___x_2132_);
lean_closure_set(v___f_2134_, 1, v_e_2128_);
lean_closure_set(v___f_2134_, 2, v___x_2133_);
lean_closure_set(v___f_2134_, 3, v_toPure_2131_);
v___x_2135_ = lean_apply_4(v_toBind_2130_, lean_box(0), lean_box(0), v_inst_2126_, v___f_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2136_, lean_object* v_t_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_e_2140_){
_start:
{
uint8_t v_pu_boxed_2141_; uint8_t v_t_boxed_2142_; lean_object* v_res_2143_; 
v_pu_boxed_2141_ = lean_unbox(v_pu_2136_);
v_t_boxed_2142_ = lean_unbox(v_t_2137_);
v_res_2143_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2141_, v_t_boxed_2142_, v_inst_2138_, v_inst_2139_, v_e_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2144_, uint8_t v_pu_2145_, uint8_t v_t_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_e_2149_){
_start:
{
lean_object* v_toApplicative_2150_; lean_object* v_toBind_2151_; lean_object* v_toPure_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; 
v_toApplicative_2150_ = lean_ctor_get(v_inst_2148_, 0);
lean_inc_ref(v_toApplicative_2150_);
v_toBind_2151_ = lean_ctor_get(v_inst_2148_, 1);
lean_inc(v_toBind_2151_);
lean_dec_ref(v_inst_2148_);
v_toPure_2152_ = lean_ctor_get(v_toApplicative_2150_, 1);
lean_inc(v_toPure_2152_);
lean_dec_ref(v_toApplicative_2150_);
v___x_2153_ = lean_box(v_pu_2145_);
v___x_2154_ = lean_box(v_t_2146_);
v___f_2155_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2155_, 0, v___x_2153_);
lean_closure_set(v___f_2155_, 1, v_e_2149_);
lean_closure_set(v___f_2155_, 2, v___x_2154_);
lean_closure_set(v___f_2155_, 3, v_toPure_2152_);
v___x_2156_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v_inst_2147_, v___f_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2157_, lean_object* v_pu_2158_, lean_object* v_t_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_e_2162_){
_start:
{
uint8_t v_pu_boxed_2163_; uint8_t v_t_boxed_2164_; lean_object* v_res_2165_; 
v_pu_boxed_2163_ = lean_unbox(v_pu_2158_);
v_t_boxed_2164_ = lean_unbox(v_t_2159_);
v_res_2165_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2157_, v_pu_boxed_2163_, v_t_boxed_2164_, v_inst_2160_, v_inst_2161_, v_e_2162_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2166_, lean_object* v_s_2167_, lean_object* v_e_2168_, uint8_t v_translator_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2166_, v_s_2167_, v_translator_2169_, v_e_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2171_, lean_object* v_s_2172_, lean_object* v_e_2173_, lean_object* v_translator_2174_){
_start:
{
uint8_t v_pu_boxed_2175_; uint8_t v_translator_boxed_2176_; lean_object* v_res_2177_; 
v_pu_boxed_2175_ = lean_unbox(v_pu_2171_);
v_translator_boxed_2176_ = lean_unbox(v_translator_2174_);
v_res_2177_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2175_, v_s_2172_, v_e_2173_, v_translator_boxed_2176_);
lean_dec_ref(v_s_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2178_, lean_object* v_args_2179_, uint8_t v_t_2180_, lean_object* v_toPure_2181_, lean_object* v_____do__lift_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2178_, v_____do__lift_2182_, v_args_2179_, v_t_2180_);
v___x_2184_ = lean_apply_2(v_toPure_2181_, lean_box(0), v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2185_, lean_object* v_args_2186_, lean_object* v_t_2187_, lean_object* v_toPure_2188_, lean_object* v_____do__lift_2189_){
_start:
{
uint8_t v_pu_boxed_2190_; uint8_t v_t_boxed_2191_; lean_object* v_res_2192_; 
v_pu_boxed_2190_ = lean_unbox(v_pu_2185_);
v_t_boxed_2191_ = lean_unbox(v_t_2187_);
v_res_2192_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2190_, v_args_2186_, v_t_boxed_2191_, v_toPure_2188_, v_____do__lift_2189_);
lean_dec_ref(v_____do__lift_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2193_, uint8_t v_t_2194_, lean_object* v_inst_2195_, lean_object* v_inst_2196_, lean_object* v_args_2197_){
_start:
{
lean_object* v_toApplicative_2198_; lean_object* v_toBind_2199_; lean_object* v_toPure_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
v_toApplicative_2198_ = lean_ctor_get(v_inst_2196_, 0);
lean_inc_ref(v_toApplicative_2198_);
v_toBind_2199_ = lean_ctor_get(v_inst_2196_, 1);
lean_inc(v_toBind_2199_);
lean_dec_ref(v_inst_2196_);
v_toPure_2200_ = lean_ctor_get(v_toApplicative_2198_, 1);
lean_inc(v_toPure_2200_);
lean_dec_ref(v_toApplicative_2198_);
v___x_2201_ = lean_box(v_pu_2193_);
v___x_2202_ = lean_box(v_t_2194_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2203_, 0, v___x_2201_);
lean_closure_set(v___f_2203_, 1, v_args_2197_);
lean_closure_set(v___f_2203_, 2, v___x_2202_);
lean_closure_set(v___f_2203_, 3, v_toPure_2200_);
v___x_2204_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v_inst_2195_, v___f_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2205_, lean_object* v_t_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_args_2209_){
_start:
{
uint8_t v_pu_boxed_2210_; uint8_t v_t_boxed_2211_; lean_object* v_res_2212_; 
v_pu_boxed_2210_ = lean_unbox(v_pu_2205_);
v_t_boxed_2211_ = lean_unbox(v_t_2206_);
v_res_2212_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2210_, v_t_boxed_2211_, v_inst_2207_, v_inst_2208_, v_args_2209_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2213_, uint8_t v_pu_2214_, uint8_t v_t_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_args_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2214_, v_t_2215_, v_inst_2216_, v_inst_2217_, v_args_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2220_, lean_object* v_pu_2221_, lean_object* v_t_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_args_2225_){
_start:
{
uint8_t v_pu_boxed_2226_; uint8_t v_t_boxed_2227_; lean_object* v_res_2228_; 
v_pu_boxed_2226_ = lean_unbox(v_pu_2221_);
v_t_boxed_2227_ = lean_unbox(v_t_2222_);
v_res_2228_ = l_Lean_Compiler_LCNF_normArgs(v_m_2220_, v_pu_boxed_2226_, v_t_boxed_2227_, v_inst_2223_, v_inst_2224_, v_args_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v_nextIdx_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_lctx_2236_; lean_object* v_nextIdx_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2248_; 
v___x_2232_ = lean_st_ref_get(v_a_2230_);
v_nextIdx_2233_ = lean_ctor_get(v___x_2232_, 1);
lean_inc(v_nextIdx_2233_);
lean_dec(v___x_2232_);
v___x_2234_ = l_Lean_Name_num___override(v_binderName_2229_, v_nextIdx_2233_);
v___x_2235_ = lean_st_ref_take(v_a_2230_);
v_lctx_2236_ = lean_ctor_get(v___x_2235_, 0);
v_nextIdx_2237_ = lean_ctor_get(v___x_2235_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2239_ = v___x_2235_;
v_isShared_2240_ = v_isSharedCheck_2248_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_nextIdx_2237_);
lean_inc(v_lctx_2236_);
lean_dec(v___x_2235_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2248_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = lean_unsigned_to_nat(1u);
v___x_2242_ = lean_nat_add(v_nextIdx_2237_, v___x_2241_);
lean_dec(v_nextIdx_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 1, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_lctx_2236_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_st_ref_put(v_a_2230_, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2234_);
return v___x_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2249_, v_a_2250_);
lean_dec(v_a_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2253_, v_a_2255_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2267_, lean_object* v_baseName_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Name_isAnonymous(v_binderName_2267_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v_baseName_2268_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_binderName_2267_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
lean_dec(v_binderName_2267_);
v___x_2273_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2268_, v_a_2269_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2274_, lean_object* v_baseName_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2274_, v_baseName_2275_, v_a_2276_);
lean_dec(v_a_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2279_, lean_object* v_baseName_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2279_, v_baseName_2280_, v_a_2282_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2287_, lean_object* v_baseName_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2287_, v_baseName_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v_ngen_2298_; lean_object* v_namePrefix_2299_; lean_object* v_idx_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2330_; 
v___x_2297_ = lean_st_ref_get(v___y_2295_);
v_ngen_2298_ = lean_ctor_get(v___x_2297_, 2);
lean_inc_ref(v_ngen_2298_);
lean_dec(v___x_2297_);
v_namePrefix_2299_ = lean_ctor_get(v_ngen_2298_, 0);
v_idx_2300_ = lean_ctor_get(v_ngen_2298_, 1);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_ngen_2298_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2302_ = v_ngen_2298_;
v_isShared_2303_ = v_isSharedCheck_2330_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_idx_2300_);
lean_inc(v_namePrefix_2299_);
lean_dec(v_ngen_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2330_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_r_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_inc(v_idx_2300_);
lean_inc(v_namePrefix_2299_);
v_r_2304_ = l_Lean_Name_num___override(v_namePrefix_2299_, v_idx_2300_);
v___x_2305_ = lean_unsigned_to_nat(1u);
v___x_2306_ = lean_nat_add(v_idx_2300_, v___x_2305_);
lean_dec(v_idx_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2306_);
v___x_2308_ = v___x_2302_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_namePrefix_2299_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; lean_object* v_env_2310_; lean_object* v_nextMacroScope_2311_; lean_object* v_auxDeclNGen_2312_; lean_object* v_traceState_2313_; lean_object* v_cache_2314_; lean_object* v_recordedDeps_2315_; lean_object* v_messages_2316_; lean_object* v_infoState_2317_; lean_object* v_snapshotTasks_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2327_; 
v___x_2309_ = lean_st_ref_take(v___y_2295_);
v_env_2310_ = lean_ctor_get(v___x_2309_, 0);
v_nextMacroScope_2311_ = lean_ctor_get(v___x_2309_, 1);
v_auxDeclNGen_2312_ = lean_ctor_get(v___x_2309_, 3);
v_traceState_2313_ = lean_ctor_get(v___x_2309_, 4);
v_cache_2314_ = lean_ctor_get(v___x_2309_, 5);
v_recordedDeps_2315_ = lean_ctor_get(v___x_2309_, 6);
v_messages_2316_ = lean_ctor_get(v___x_2309_, 7);
v_infoState_2317_ = lean_ctor_get(v___x_2309_, 8);
v_snapshotTasks_2318_ = lean_ctor_get(v___x_2309_, 9);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v___x_2309_, 2);
lean_dec(v_unused_2328_);
v___x_2320_ = v___x_2309_;
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_snapshotTasks_2318_);
lean_inc(v_infoState_2317_);
lean_inc(v_messages_2316_);
lean_inc(v_recordedDeps_2315_);
lean_inc(v_cache_2314_);
lean_inc(v_traceState_2313_);
lean_inc(v_auxDeclNGen_2312_);
lean_inc(v_nextMacroScope_2311_);
lean_inc(v_env_2310_);
lean_dec(v___x_2309_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 2, v___x_2308_);
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_env_2310_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_nextMacroScope_2311_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_auxDeclNGen_2312_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_traceState_2313_);
lean_ctor_set(v_reuseFailAlloc_2326_, 5, v_cache_2314_);
lean_ctor_set(v_reuseFailAlloc_2326_, 6, v_recordedDeps_2315_);
lean_ctor_set(v_reuseFailAlloc_2326_, 7, v_messages_2316_);
lean_ctor_set(v_reuseFailAlloc_2326_, 8, v_infoState_2317_);
lean_ctor_set(v_reuseFailAlloc_2326_, 9, v_snapshotTasks_2318_);
v___x_2323_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_st_ref_put(v___y_2295_, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_r_2304_);
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2331_);
lean_dec(v___y_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v___x_2339_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2337_);
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2357_, lean_object* v_binderName_2358_, lean_object* v_type_2359_, uint8_t v_borrow_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2390_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2369_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2358_, v___x_2368_, v_a_2362_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2390_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2390_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_lctx_2376_; lean_object* v_nextIdx_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2389_; 
v___x_2374_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2374_, 0, v_a_2367_);
lean_ctor_set(v___x_2374_, 1, v_a_2370_);
lean_ctor_set(v___x_2374_, 2, v_type_2359_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*3, v_borrow_2360_);
v___x_2375_ = lean_st_ref_take(v_a_2362_);
v_lctx_2376_ = lean_ctor_get(v___x_2375_, 0);
v_nextIdx_2377_ = lean_ctor_get(v___x_2375_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2379_ = v___x_2375_;
v_isShared_2380_ = v_isSharedCheck_2389_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_nextIdx_2377_);
lean_inc(v_lctx_2376_);
lean_dec(v___x_2375_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2389_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_inc_ref(v___x_2374_);
v___x_2381_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2357_, v_lctx_2376_, v___x_2374_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_nextIdx_2377_);
v___x_2383_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_st_ref_put(v_a_2362_, v___x_2383_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2374_);
v___x_2386_ = v___x_2372_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2374_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_type_2359_);
lean_dec(v_binderName_2358_);
v_a_2391_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2366_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2366_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2399_, lean_object* v_binderName_2400_, lean_object* v_type_2401_, lean_object* v_borrow_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
uint8_t v_pu_boxed_2408_; uint8_t v_borrow_boxed_2409_; lean_object* v_res_2410_; 
v_pu_boxed_2408_ = lean_unbox(v_pu_2399_);
v_borrow_boxed_2409_ = lean_unbox(v_borrow_2402_);
v_res_2410_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2408_, v_binderName_2400_, v_type_2401_, v_borrow_boxed_2409_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2426_, lean_object* v_binderName_2427_, lean_object* v_type_2428_, lean_object* v_value_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2459_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2438_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2427_, v___x_2437_, v_a_2431_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2459_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2459_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_lctx_2445_; lean_object* v_nextIdx_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2458_; 
v___x_2443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2443_, 0, v_a_2436_);
lean_ctor_set(v___x_2443_, 1, v_a_2439_);
lean_ctor_set(v___x_2443_, 2, v_type_2428_);
lean_ctor_set(v___x_2443_, 3, v_value_2429_);
v___x_2444_ = lean_st_ref_take(v_a_2431_);
v_lctx_2445_ = lean_ctor_get(v___x_2444_, 0);
v_nextIdx_2446_ = lean_ctor_get(v___x_2444_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2448_ = v___x_2444_;
v_isShared_2449_ = v_isSharedCheck_2458_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_nextIdx_2446_);
lean_inc(v_lctx_2445_);
lean_dec(v___x_2444_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2458_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_inc_ref(v___x_2443_);
v___x_2450_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2426_, v_lctx_2445_, v___x_2443_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_nextIdx_2446_);
v___x_2452_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = lean_st_ref_put(v_a_2431_, v___x_2452_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2443_);
v___x_2455_ = v___x_2441_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2443_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_value_2429_);
lean_dec_ref(v_type_2428_);
lean_dec(v_binderName_2427_);
v_a_2460_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2435_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2435_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2468_, lean_object* v_binderName_2469_, lean_object* v_type_2470_, lean_object* v_value_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
uint8_t v_pu_boxed_2477_; lean_object* v_res_2478_; 
v_pu_boxed_2477_ = lean_unbox(v_pu_2468_);
v_res_2478_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2477_, v_binderName_2469_, v_type_2470_, v_value_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2482_, lean_object* v_binderName_2483_, lean_object* v_type_2484_, lean_object* v_params_2485_, lean_object* v_value_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2516_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2495_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2483_, v___x_2494_, v_a_2488_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2516_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2516_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v_lctx_2502_; lean_object* v_nextIdx_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2515_; 
v___x_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2493_);
lean_ctor_set(v___x_2500_, 1, v_a_2496_);
lean_ctor_set(v___x_2500_, 2, v_params_2485_);
lean_ctor_set(v___x_2500_, 3, v_type_2484_);
lean_ctor_set(v___x_2500_, 4, v_value_2486_);
v___x_2501_ = lean_st_ref_take(v_a_2488_);
v_lctx_2502_ = lean_ctor_get(v___x_2501_, 0);
v_nextIdx_2503_ = lean_ctor_get(v___x_2501_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2505_ = v___x_2501_;
v_isShared_2506_ = v_isSharedCheck_2515_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_nextIdx_2503_);
lean_inc(v_lctx_2502_);
lean_dec(v___x_2501_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2515_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_inc_ref(v___x_2500_);
v___x_2507_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2482_, v_lctx_2502_, v___x_2500_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_nextIdx_2503_);
v___x_2509_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_st_ref_put(v_a_2488_, v___x_2509_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2500_);
v___x_2512_ = v___x_2498_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2500_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_value_2486_);
lean_dec_ref(v_params_2485_);
lean_dec_ref(v_type_2484_);
lean_dec(v_binderName_2483_);
v_a_2517_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2492_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2492_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2525_, lean_object* v_binderName_2526_, lean_object* v_type_2527_, lean_object* v_params_2528_, lean_object* v_value_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
uint8_t v_pu_boxed_2535_; lean_object* v_res_2536_; 
v_pu_boxed_2535_ = lean_unbox(v_pu_2525_);
v_res_2536_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2535_, v_binderName_2526_, v_type_2527_, v_params_2528_, v_value_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2544_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2543_, v_a_2539_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2547_ = lean_box(1);
v___x_2548_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2537_, v_a_2545_, v___x_2546_, v___x_2547_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
uint8_t v_pu_boxed_2555_; lean_object* v_res_2556_; 
v_pu_boxed_2555_ = lean_unbox(v_pu_2549_);
v_res_2556_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2555_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2574_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2574_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2574_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_fvarId_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v_fvarId_2568_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_fvarId_2568_);
v___x_2569_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_fvarId_2568_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2564_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2570_);
v___x_2572_ = v___x_2566_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2563_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2563_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v_pu_boxed_2589_; lean_object* v_res_2590_; 
v_pu_boxed_2589_ = lean_unbox(v_pu_2583_);
v_res_2590_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2589_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2591_, lean_object* v_p_2592_, lean_object* v_type_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_fvarId_2596_; lean_object* v_binderName_2597_; lean_object* v_type_2598_; uint8_t v_borrow_2599_; size_t v___x_2600_; size_t v___x_2601_; uint8_t v___x_2602_; 
v_fvarId_2596_ = lean_ctor_get(v_p_2592_, 0);
v_binderName_2597_ = lean_ctor_get(v_p_2592_, 1);
v_type_2598_ = lean_ctor_get(v_p_2592_, 2);
v_borrow_2599_ = lean_ctor_get_uint8(v_p_2592_, sizeof(void*)*3);
v___x_2600_ = lean_ptr_addr(v_type_2593_);
v___x_2601_ = lean_ptr_addr(v_type_2598_);
v___x_2602_ = lean_usize_dec_eq(v___x_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2622_; 
lean_inc(v_binderName_2597_);
lean_inc(v_fvarId_2596_);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_p_2592_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; lean_object* v_unused_2624_; lean_object* v_unused_2625_; 
v_unused_2623_ = lean_ctor_get(v_p_2592_, 2);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_p_2592_, 1);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_p_2592_, 0);
lean_dec(v_unused_2625_);
v___x_2604_ = v_p_2592_;
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v_p_2592_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_p_2607_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 2, v_type_2593_);
v_p_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_fvarId_2596_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_binderName_2597_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_type_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2621_, sizeof(void*)*3, v_borrow_2599_);
v_p_2607_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v_lctx_2609_; lean_object* v_nextIdx_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2620_; 
v___x_2608_ = lean_st_ref_take(v_a_2594_);
v_lctx_2609_ = lean_ctor_get(v___x_2608_, 0);
v_nextIdx_2610_ = lean_ctor_get(v___x_2608_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2612_ = v___x_2608_;
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_nextIdx_2610_);
lean_inc(v_lctx_2609_);
lean_dec(v___x_2608_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_inc_ref(v_p_2607_);
v___x_2614_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2591_, v_lctx_2609_, v_p_2607_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_nextIdx_2610_);
v___x_2616_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_st_ref_put(v_a_2594_, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_p_2607_);
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v___x_2626_; 
lean_dec_ref(v_type_2593_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_p_2592_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2627_, lean_object* v_p_2628_, lean_object* v_type_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
uint8_t v_pu_boxed_2632_; lean_object* v_res_2633_; 
v_pu_boxed_2632_ = lean_unbox(v_pu_2627_);
v_res_2633_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2632_, v_p_2628_, v_type_2629_, v_a_2630_);
lean_dec(v_a_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2634_, lean_object* v_p_2635_, lean_object* v_type_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2634_, v_p_2635_, v_type_2636_, v_a_2638_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2643_, lean_object* v_p_2644_, lean_object* v_type_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
uint8_t v_pu_boxed_2651_; lean_object* v_res_2652_; 
v_pu_boxed_2651_ = lean_unbox(v_pu_2643_);
v_res_2652_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2651_, v_p_2644_, v_type_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2653_, lean_object* v_p_2654_, uint8_t v_borrow_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_fvarId_2658_; lean_object* v_binderName_2659_; lean_object* v_type_2660_; uint8_t v_borrow_2661_; 
v_fvarId_2658_ = lean_ctor_get(v_p_2654_, 0);
v_binderName_2659_ = lean_ctor_get(v_p_2654_, 1);
v_type_2660_ = lean_ctor_get(v_p_2654_, 2);
v_borrow_2661_ = lean_ctor_get_uint8(v_p_2654_, sizeof(void*)*3);
if (v_borrow_2661_ == 0)
{
if (v_borrow_2655_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_p_2654_);
return v___x_2677_;
}
else
{
lean_inc_ref(v_type_2660_);
lean_inc(v_binderName_2659_);
lean_inc(v_fvarId_2658_);
lean_dec_ref(v_p_2654_);
goto v___jp_2662_;
}
}
else
{
if (v_borrow_2655_ == 0)
{
lean_inc_ref(v_type_2660_);
lean_inc(v_binderName_2659_);
lean_inc(v_fvarId_2658_);
lean_dec_ref(v_p_2654_);
goto v___jp_2662_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_p_2654_);
return v___x_2678_;
}
}
v___jp_2662_:
{
lean_object* v_p_2663_; lean_object* v___x_2664_; lean_object* v_lctx_2665_; lean_object* v_nextIdx_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2676_; 
v_p_2663_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2663_, 0, v_fvarId_2658_);
lean_ctor_set(v_p_2663_, 1, v_binderName_2659_);
lean_ctor_set(v_p_2663_, 2, v_type_2660_);
lean_ctor_set_uint8(v_p_2663_, sizeof(void*)*3, v_borrow_2655_);
v___x_2664_ = lean_st_ref_take(v_a_2656_);
v_lctx_2665_ = lean_ctor_get(v___x_2664_, 0);
v_nextIdx_2666_ = lean_ctor_get(v___x_2664_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2668_ = v___x_2664_;
v_isShared_2669_ = v_isSharedCheck_2676_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_nextIdx_2666_);
lean_inc(v_lctx_2665_);
lean_dec(v___x_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2676_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_inc_ref(v_p_2663_);
v___x_2670_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2653_, v_lctx_2665_, v_p_2663_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_nextIdx_2666_);
v___x_2672_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_st_ref_put(v_a_2656_, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_p_2663_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2679_, lean_object* v_p_2680_, lean_object* v_borrow_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_pu_boxed_2684_; uint8_t v_borrow_boxed_2685_; lean_object* v_res_2686_; 
v_pu_boxed_2684_ = lean_unbox(v_pu_2679_);
v_borrow_boxed_2685_ = lean_unbox(v_borrow_2681_);
v_res_2686_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2684_, v_p_2680_, v_borrow_boxed_2685_, v_a_2682_);
lean_dec(v_a_2682_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2687_, lean_object* v_p_2688_, uint8_t v_borrow_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2687_, v_p_2688_, v_borrow_2689_, v_a_2691_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2696_, lean_object* v_p_2697_, lean_object* v_borrow_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
uint8_t v_pu_boxed_2704_; uint8_t v_borrow_boxed_2705_; lean_object* v_res_2706_; 
v_pu_boxed_2704_ = lean_unbox(v_pu_2696_);
v_borrow_boxed_2705_ = lean_unbox(v_borrow_2698_);
v_res_2706_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2704_, v_p_2697_, v_borrow_boxed_2705_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2707_, lean_object* v_decl_2708_, lean_object* v_type_2709_, lean_object* v_value_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_fvarId_2713_; lean_object* v_binderName_2714_; lean_object* v_type_2715_; lean_object* v_value_2716_; size_t v___x_2732_; size_t v___x_2733_; uint8_t v___x_2734_; 
v_fvarId_2713_ = lean_ctor_get(v_decl_2708_, 0);
v_binderName_2714_ = lean_ctor_get(v_decl_2708_, 1);
v_type_2715_ = lean_ctor_get(v_decl_2708_, 2);
v_value_2716_ = lean_ctor_get(v_decl_2708_, 3);
v___x_2732_ = lean_ptr_addr(v_type_2709_);
v___x_2733_ = lean_ptr_addr(v_type_2715_);
v___x_2734_ = lean_usize_dec_eq(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_inc(v_binderName_2714_);
lean_inc(v_fvarId_2713_);
lean_dec_ref(v_decl_2708_);
goto v___jp_2717_;
}
else
{
size_t v___x_2735_; size_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_ptr_addr(v_value_2710_);
v___x_2736_ = lean_ptr_addr(v_value_2716_);
v___x_2737_ = lean_usize_dec_eq(v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_inc(v_binderName_2714_);
lean_inc(v_fvarId_2713_);
lean_dec_ref(v_decl_2708_);
goto v___jp_2717_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v_value_2710_);
lean_dec_ref(v_type_2709_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_decl_2708_);
return v___x_2738_;
}
}
v___jp_2717_:
{
lean_object* v_decl_2718_; lean_object* v___x_2719_; lean_object* v_lctx_2720_; lean_object* v_nextIdx_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2731_; 
v_decl_2718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2718_, 0, v_fvarId_2713_);
lean_ctor_set(v_decl_2718_, 1, v_binderName_2714_);
lean_ctor_set(v_decl_2718_, 2, v_type_2709_);
lean_ctor_set(v_decl_2718_, 3, v_value_2710_);
v___x_2719_ = lean_st_ref_take(v_a_2711_);
v_lctx_2720_ = lean_ctor_get(v___x_2719_, 0);
v_nextIdx_2721_ = lean_ctor_get(v___x_2719_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2723_ = v___x_2719_;
v_isShared_2724_ = v_isSharedCheck_2731_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_nextIdx_2721_);
lean_inc(v_lctx_2720_);
lean_dec(v___x_2719_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2731_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc_ref(v_decl_2718_);
v___x_2725_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2707_, v_lctx_2720_, v_decl_2718_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_nextIdx_2721_);
v___x_2727_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_st_ref_put(v_a_2711_, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v_decl_2718_);
return v___x_2729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2739_, lean_object* v_decl_2740_, lean_object* v_type_2741_, lean_object* v_value_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
uint8_t v_pu_boxed_2745_; lean_object* v_res_2746_; 
v_pu_boxed_2745_ = lean_unbox(v_pu_2739_);
v_res_2746_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2745_, v_decl_2740_, v_type_2741_, v_value_2742_, v_a_2743_);
lean_dec(v_a_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2747_, lean_object* v_decl_2748_, lean_object* v_type_2749_, lean_object* v_value_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2747_, v_decl_2748_, v_type_2749_, v_value_2750_, v_a_2752_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2757_, lean_object* v_decl_2758_, lean_object* v_type_2759_, lean_object* v_value_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
uint8_t v_pu_boxed_2766_; lean_object* v_res_2767_; 
v_pu_boxed_2766_ = lean_unbox(v_pu_2757_);
v_res_2767_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2766_, v_decl_2758_, v_type_2759_, v_value_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2768_, lean_object* v_decl_2769_, lean_object* v_value_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_type_2773_; lean_object* v___x_2774_; 
v_type_2773_ = lean_ctor_get(v_decl_2769_, 2);
lean_inc_ref(v_type_2773_);
v___x_2774_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2768_, v_decl_2769_, v_type_2773_, v_value_2770_, v_a_2771_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2775_, lean_object* v_decl_2776_, lean_object* v_value_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
uint8_t v_pu_boxed_2780_; lean_object* v_res_2781_; 
v_pu_boxed_2780_ = lean_unbox(v_pu_2775_);
v_res_2781_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2780_, v_decl_2776_, v_value_2777_, v_a_2778_);
lean_dec(v_a_2778_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2782_, lean_object* v_decl_2783_, lean_object* v_value_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2782_, v_decl_2783_, v_value_2784_, v_a_2786_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2791_, lean_object* v_decl_2792_, lean_object* v_value_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
uint8_t v_pu_boxed_2799_; lean_object* v_res_2800_; 
v_pu_boxed_2799_ = lean_unbox(v_pu_2791_);
v_res_2800_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2799_, v_decl_2792_, v_value_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2801_, lean_object* v_decl_2802_, lean_object* v_type_2803_, lean_object* v_params_2804_, lean_object* v_value_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_fvarId_2808_; lean_object* v_binderName_2809_; lean_object* v_params_2810_; lean_object* v_type_2811_; lean_object* v_value_2812_; size_t v___x_2828_; size_t v___x_2829_; uint8_t v___x_2830_; 
v_fvarId_2808_ = lean_ctor_get(v_decl_2802_, 0);
v_binderName_2809_ = lean_ctor_get(v_decl_2802_, 1);
v_params_2810_ = lean_ctor_get(v_decl_2802_, 2);
v_type_2811_ = lean_ctor_get(v_decl_2802_, 3);
v_value_2812_ = lean_ctor_get(v_decl_2802_, 4);
v___x_2828_ = lean_ptr_addr(v_type_2803_);
v___x_2829_ = lean_ptr_addr(v_type_2811_);
v___x_2830_ = lean_usize_dec_eq(v___x_2828_, v___x_2829_);
if (v___x_2830_ == 0)
{
lean_inc(v_binderName_2809_);
lean_inc(v_fvarId_2808_);
lean_dec_ref(v_decl_2802_);
goto v___jp_2813_;
}
else
{
size_t v___x_2831_; size_t v___x_2832_; uint8_t v___x_2833_; 
v___x_2831_ = lean_ptr_addr(v_params_2804_);
v___x_2832_ = lean_ptr_addr(v_params_2810_);
v___x_2833_ = lean_usize_dec_eq(v___x_2831_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_inc(v_binderName_2809_);
lean_inc(v_fvarId_2808_);
lean_dec_ref(v_decl_2802_);
goto v___jp_2813_;
}
else
{
size_t v___x_2834_; size_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = lean_ptr_addr(v_value_2805_);
v___x_2835_ = lean_ptr_addr(v_value_2812_);
v___x_2836_ = lean_usize_dec_eq(v___x_2834_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_inc(v_binderName_2809_);
lean_inc(v_fvarId_2808_);
lean_dec_ref(v_decl_2802_);
goto v___jp_2813_;
}
else
{
lean_object* v___x_2837_; 
lean_dec_ref(v_value_2805_);
lean_dec_ref(v_params_2804_);
lean_dec_ref(v_type_2803_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_decl_2802_);
return v___x_2837_;
}
}
}
v___jp_2813_:
{
lean_object* v_decl_2814_; lean_object* v___x_2815_; lean_object* v_lctx_2816_; lean_object* v_nextIdx_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2827_; 
v_decl_2814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2814_, 0, v_fvarId_2808_);
lean_ctor_set(v_decl_2814_, 1, v_binderName_2809_);
lean_ctor_set(v_decl_2814_, 2, v_params_2804_);
lean_ctor_set(v_decl_2814_, 3, v_type_2803_);
lean_ctor_set(v_decl_2814_, 4, v_value_2805_);
v___x_2815_ = lean_st_ref_take(v_a_2806_);
v_lctx_2816_ = lean_ctor_get(v___x_2815_, 0);
v_nextIdx_2817_ = lean_ctor_get(v___x_2815_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2819_ = v___x_2815_;
v_isShared_2820_ = v_isSharedCheck_2827_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_nextIdx_2817_);
lean_inc(v_lctx_2816_);
lean_dec(v___x_2815_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2827_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
lean_inc_ref(v_decl_2814_);
v___x_2821_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2801_, v_lctx_2816_, v_decl_2814_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2821_);
v___x_2823_ = v___x_2819_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_nextIdx_2817_);
v___x_2823_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_st_ref_put(v_a_2806_, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_decl_2814_);
return v___x_2825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2838_, lean_object* v_decl_2839_, lean_object* v_type_2840_, lean_object* v_params_2841_, lean_object* v_value_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
uint8_t v_pu_boxed_2845_; lean_object* v_res_2846_; 
v_pu_boxed_2845_ = lean_unbox(v_pu_2838_);
v_res_2846_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2845_, v_decl_2839_, v_type_2840_, v_params_2841_, v_value_2842_, v_a_2843_);
lean_dec(v_a_2843_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2847_, lean_object* v_decl_2848_, lean_object* v_type_2849_, lean_object* v_params_2850_, lean_object* v_value_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2847_, v_decl_2848_, v_type_2849_, v_params_2850_, v_value_2851_, v_a_2853_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2858_, lean_object* v_decl_2859_, lean_object* v_type_2860_, lean_object* v_params_2861_, lean_object* v_value_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
uint8_t v_pu_boxed_2868_; lean_object* v_res_2869_; 
v_pu_boxed_2868_ = lean_unbox(v_pu_2858_);
v_res_2869_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2868_, v_decl_2859_, v_type_2860_, v_params_2861_, v_value_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2870_, lean_object* v_decl_2871_, lean_object* v_type_2872_, lean_object* v_value_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_params_2876_; lean_object* v___x_2877_; 
v_params_2876_ = lean_ctor_get(v_decl_2871_, 2);
lean_inc_ref(v_params_2876_);
v___x_2877_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2870_, v_decl_2871_, v_type_2872_, v_params_2876_, v_value_2873_, v_a_2874_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2878_, lean_object* v_decl_2879_, lean_object* v_type_2880_, lean_object* v_value_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
uint8_t v_pu_boxed_2884_; lean_object* v_res_2885_; 
v_pu_boxed_2884_ = lean_unbox(v_pu_2878_);
v_res_2885_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2884_, v_decl_2879_, v_type_2880_, v_value_2881_, v_a_2882_);
lean_dec(v_a_2882_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2886_, lean_object* v_decl_2887_, lean_object* v_type_2888_, lean_object* v_value_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_params_2895_; lean_object* v___x_2896_; 
v_params_2895_ = lean_ctor_get(v_decl_2887_, 2);
lean_inc_ref(v_params_2895_);
v___x_2896_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2886_, v_decl_2887_, v_type_2888_, v_params_2895_, v_value_2889_, v_a_2891_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2897_, lean_object* v_decl_2898_, lean_object* v_type_2899_, lean_object* v_value_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
uint8_t v_pu_boxed_2906_; lean_object* v_res_2907_; 
v_pu_boxed_2906_ = lean_unbox(v_pu_2897_);
v_res_2907_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2906_, v_decl_2898_, v_type_2899_, v_value_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2908_, lean_object* v_decl_2909_, lean_object* v_value_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_params_2913_; lean_object* v_type_2914_; lean_object* v___x_2915_; 
v_params_2913_ = lean_ctor_get(v_decl_2909_, 2);
lean_inc_ref(v_params_2913_);
v_type_2914_ = lean_ctor_get(v_decl_2909_, 3);
lean_inc_ref(v_type_2914_);
v___x_2915_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2908_, v_decl_2909_, v_type_2914_, v_params_2913_, v_value_2910_, v_a_2911_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2916_, lean_object* v_decl_2917_, lean_object* v_value_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
uint8_t v_pu_boxed_2921_; lean_object* v_res_2922_; 
v_pu_boxed_2921_ = lean_unbox(v_pu_2916_);
v_res_2922_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2921_, v_decl_2917_, v_value_2918_, v_a_2919_);
lean_dec(v_a_2919_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2923_, lean_object* v_decl_2924_, lean_object* v_value_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_params_2931_; lean_object* v_type_2932_; lean_object* v___x_2933_; 
v_params_2931_ = lean_ctor_get(v_decl_2924_, 2);
lean_inc_ref(v_params_2931_);
v_type_2932_ = lean_ctor_get(v_decl_2924_, 3);
lean_inc_ref(v_type_2932_);
v___x_2933_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2923_, v_decl_2924_, v_type_2932_, v_params_2931_, v_value_2925_, v_a_2927_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2934_, lean_object* v_decl_2935_, lean_object* v_value_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
uint8_t v_pu_boxed_2942_; lean_object* v_res_2943_; 
v_pu_boxed_2942_ = lean_unbox(v_pu_2934_);
v_res_2943_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2942_, v_decl_2935_, v_value_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2944_, lean_object* v_p_2945_, lean_object* v_inst_2946_, lean_object* v_____do__lift_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_box(v_pu_2944_);
v___x_2949_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2949_, 0, v___x_2948_);
lean_closure_set(v___x_2949_, 1, v_p_2945_);
lean_closure_set(v___x_2949_, 2, v_____do__lift_2947_);
v___x_2950_ = lean_apply_2(v_inst_2946_, lean_box(0), v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2951_, lean_object* v_p_2952_, lean_object* v_inst_2953_, lean_object* v_____do__lift_2954_){
_start:
{
uint8_t v_pu_boxed_2955_; lean_object* v_res_2956_; 
v_pu_boxed_2955_ = lean_unbox(v_pu_2951_);
v_res_2956_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2955_, v_p_2952_, v_inst_2953_, v_____do__lift_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2957_, uint8_t v_t_2958_, lean_object* v_type_2959_, lean_object* v_toPure_2960_, lean_object* v_____do__lift_2961_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2957_, v_____do__lift_2961_, v_t_2958_, v_type_2959_);
v___x_2963_ = lean_apply_2(v_toPure_2960_, lean_box(0), v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2964_, lean_object* v_t_2965_, lean_object* v_type_2966_, lean_object* v_toPure_2967_, lean_object* v_____do__lift_2968_){
_start:
{
uint8_t v_pu_boxed_2969_; uint8_t v_t_boxed_2970_; lean_object* v_res_2971_; 
v_pu_boxed_2969_ = lean_unbox(v_pu_2964_);
v_t_boxed_2970_ = lean_unbox(v_t_2965_);
v_res_2971_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2969_, v_t_boxed_2970_, v_type_2966_, v_toPure_2967_, v_____do__lift_2968_);
lean_dec_ref(v_____do__lift_2968_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2972_, uint8_t v_t_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_p_2977_){
_start:
{
lean_object* v_toApplicative_2978_; lean_object* v_toBind_2979_; lean_object* v_type_2980_; lean_object* v_toPure_2981_; lean_object* v___x_2982_; lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_toApplicative_2978_ = lean_ctor_get(v_inst_2975_, 0);
lean_inc_ref(v_toApplicative_2978_);
v_toBind_2979_ = lean_ctor_get(v_inst_2975_, 1);
lean_inc_n(v_toBind_2979_, 2);
lean_dec_ref(v_inst_2975_);
v_type_2980_ = lean_ctor_get(v_p_2977_, 2);
lean_inc_ref(v_type_2980_);
v_toPure_2981_ = lean_ctor_get(v_toApplicative_2978_, 1);
lean_inc(v_toPure_2981_);
lean_dec_ref(v_toApplicative_2978_);
v___x_2982_ = lean_box(v_pu_2972_);
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2983_, 0, v___x_2982_);
lean_closure_set(v___f_2983_, 1, v_p_2977_);
lean_closure_set(v___f_2983_, 2, v_inst_2974_);
v___x_2984_ = lean_box(v_pu_2972_);
v___x_2985_ = lean_box(v_t_2973_);
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2986_, 0, v___x_2984_);
lean_closure_set(v___f_2986_, 1, v___x_2985_);
lean_closure_set(v___f_2986_, 2, v_type_2980_);
lean_closure_set(v___f_2986_, 3, v_toPure_2981_);
v___x_2987_ = lean_apply_4(v_toBind_2979_, lean_box(0), lean_box(0), v_inst_2976_, v___f_2986_);
v___x_2988_ = lean_apply_4(v_toBind_2979_, lean_box(0), lean_box(0), v___x_2987_, v___f_2983_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2989_, lean_object* v_t_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_p_2994_){
_start:
{
uint8_t v_pu_boxed_2995_; uint8_t v_t_boxed_2996_; lean_object* v_res_2997_; 
v_pu_boxed_2995_ = lean_unbox(v_pu_2989_);
v_t_boxed_2996_ = lean_unbox(v_t_2990_);
v_res_2997_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_2995_, v_t_boxed_2996_, v_inst_2991_, v_inst_2992_, v_inst_2993_, v_p_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_2998_, uint8_t v_pu_2999_, uint8_t v_t_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_p_3004_){
_start:
{
lean_object* v_toApplicative_3005_; lean_object* v_toBind_3006_; lean_object* v_type_3007_; lean_object* v_toPure_3008_; lean_object* v___x_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___f_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_toApplicative_3005_ = lean_ctor_get(v_inst_3002_, 0);
lean_inc_ref(v_toApplicative_3005_);
v_toBind_3006_ = lean_ctor_get(v_inst_3002_, 1);
lean_inc_n(v_toBind_3006_, 2);
lean_dec_ref(v_inst_3002_);
v_type_3007_ = lean_ctor_get(v_p_3004_, 2);
lean_inc_ref(v_type_3007_);
v_toPure_3008_ = lean_ctor_get(v_toApplicative_3005_, 1);
lean_inc(v_toPure_3008_);
lean_dec_ref(v_toApplicative_3005_);
v___x_3009_ = lean_box(v_pu_2999_);
v___f_3010_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3010_, 0, v___x_3009_);
lean_closure_set(v___f_3010_, 1, v_p_3004_);
lean_closure_set(v___f_3010_, 2, v_inst_3001_);
v___x_3011_ = lean_box(v_pu_2999_);
v___x_3012_ = lean_box(v_t_3000_);
v___f_3013_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3013_, 0, v___x_3011_);
lean_closure_set(v___f_3013_, 1, v___x_3012_);
lean_closure_set(v___f_3013_, 2, v_type_3007_);
lean_closure_set(v___f_3013_, 3, v_toPure_3008_);
v___x_3014_ = lean_apply_4(v_toBind_3006_, lean_box(0), lean_box(0), v_inst_3003_, v___f_3013_);
v___x_3015_ = lean_apply_4(v_toBind_3006_, lean_box(0), lean_box(0), v___x_3014_, v___f_3010_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3016_, lean_object* v_pu_3017_, lean_object* v_t_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_p_3022_){
_start:
{
uint8_t v_pu_boxed_3023_; uint8_t v_t_boxed_3024_; lean_object* v_res_3025_; 
v_pu_boxed_3023_ = lean_unbox(v_pu_3017_);
v_t_boxed_3024_ = lean_unbox(v_t_3018_);
v_res_3025_ = l_Lean_Compiler_LCNF_normParam(v_m_3016_, v_pu_boxed_3023_, v_t_boxed_3024_, v_inst_3019_, v_inst_3020_, v_inst_3021_, v_p_3022_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3026_, uint8_t v_t_3027_, lean_object* v_inst_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_ps_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3032_ = lean_box(v_pu_3026_);
v___x_3033_ = lean_box(v_t_3027_);
lean_inc_ref(v_inst_3029_);
v___x_3034_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3034_, 0, lean_box(0));
lean_closure_set(v___x_3034_, 1, v___x_3032_);
lean_closure_set(v___x_3034_, 2, v___x_3033_);
lean_closure_set(v___x_3034_, 3, v_inst_3028_);
lean_closure_set(v___x_3034_, 4, v_inst_3029_);
lean_closure_set(v___x_3034_, 5, v_inst_3030_);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3029_, v___x_3034_, v___x_3035_, v_ps_3031_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3037_, lean_object* v_t_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_ps_3042_){
_start:
{
uint8_t v_pu_boxed_3043_; uint8_t v_t_boxed_3044_; lean_object* v_res_3045_; 
v_pu_boxed_3043_ = lean_unbox(v_pu_3037_);
v_t_boxed_3044_ = lean_unbox(v_t_3038_);
v_res_3045_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3043_, v_t_boxed_3044_, v_inst_3039_, v_inst_3040_, v_inst_3041_, v_ps_3042_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3046_, uint8_t v_pu_3047_, uint8_t v_t_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_ps_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3047_, v_t_3048_, v_inst_3049_, v_inst_3050_, v_inst_3051_, v_ps_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3054_, lean_object* v_pu_3055_, lean_object* v_t_3056_, lean_object* v_inst_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_ps_3060_){
_start:
{
uint8_t v_pu_boxed_3061_; uint8_t v_t_boxed_3062_; lean_object* v_res_3063_; 
v_pu_boxed_3061_ = lean_unbox(v_pu_3055_);
v_t_boxed_3062_ = lean_unbox(v_t_3056_);
v_res_3063_ = l_Lean_Compiler_LCNF_normParams(v_m_3054_, v_pu_boxed_3061_, v_t_boxed_3062_, v_inst_3057_, v_inst_3058_, v_inst_3059_, v_ps_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3064_, lean_object* v_decl_3065_, lean_object* v_____do__lift_3066_, lean_object* v_inst_3067_, lean_object* v_____do__lift_3068_){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_box(v_pu_3064_);
v___x_3070_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3070_, 0, v___x_3069_);
lean_closure_set(v___x_3070_, 1, v_decl_3065_);
lean_closure_set(v___x_3070_, 2, v_____do__lift_3066_);
lean_closure_set(v___x_3070_, 3, v_____do__lift_3068_);
v___x_3071_ = lean_apply_2(v_inst_3067_, lean_box(0), v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3072_, lean_object* v_decl_3073_, lean_object* v_____do__lift_3074_, lean_object* v_inst_3075_, lean_object* v_____do__lift_3076_){
_start:
{
uint8_t v_pu_boxed_3077_; lean_object* v_res_3078_; 
v_pu_boxed_3077_ = lean_unbox(v_pu_3072_);
v_res_3078_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3077_, v_decl_3073_, v_____do__lift_3074_, v_inst_3075_, v_____do__lift_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3079_, lean_object* v_value_3080_, uint8_t v_t_3081_, lean_object* v_toPure_3082_, lean_object* v_____do__lift_3083_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3079_, v_____do__lift_3083_, v_value_3080_, v_t_3081_);
v___x_3085_ = lean_apply_2(v_toPure_3082_, lean_box(0), v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3086_, lean_object* v_value_3087_, lean_object* v_t_3088_, lean_object* v_toPure_3089_, lean_object* v_____do__lift_3090_){
_start:
{
uint8_t v_pu_boxed_3091_; uint8_t v_t_boxed_3092_; lean_object* v_res_3093_; 
v_pu_boxed_3091_ = lean_unbox(v_pu_3086_);
v_t_boxed_3092_ = lean_unbox(v_t_3088_);
v_res_3093_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3091_, v_value_3087_, v_t_boxed_3092_, v_toPure_3089_, v_____do__lift_3090_);
lean_dec_ref(v_____do__lift_3090_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3094_, lean_object* v_decl_3095_, lean_object* v_inst_3096_, lean_object* v_value_3097_, uint8_t v_t_3098_, lean_object* v_toPure_3099_, lean_object* v_toBind_3100_, lean_object* v_inst_3101_, lean_object* v_____do__lift_3102_){
_start:
{
lean_object* v___x_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___f_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3103_ = lean_box(v_pu_3094_);
v___f_3104_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3104_, 0, v___x_3103_);
lean_closure_set(v___f_3104_, 1, v_decl_3095_);
lean_closure_set(v___f_3104_, 2, v_____do__lift_3102_);
lean_closure_set(v___f_3104_, 3, v_inst_3096_);
v___x_3105_ = lean_box(v_pu_3094_);
v___x_3106_ = lean_box(v_t_3098_);
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3107_, 0, v___x_3105_);
lean_closure_set(v___f_3107_, 1, v_value_3097_);
lean_closure_set(v___f_3107_, 2, v___x_3106_);
lean_closure_set(v___f_3107_, 3, v_toPure_3099_);
lean_inc(v_toBind_3100_);
v___x_3108_ = lean_apply_4(v_toBind_3100_, lean_box(0), lean_box(0), v_inst_3101_, v___f_3107_);
v___x_3109_ = lean_apply_4(v_toBind_3100_, lean_box(0), lean_box(0), v___x_3108_, v___f_3104_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3110_, lean_object* v_decl_3111_, lean_object* v_inst_3112_, lean_object* v_value_3113_, lean_object* v_t_3114_, lean_object* v_toPure_3115_, lean_object* v_toBind_3116_, lean_object* v_inst_3117_, lean_object* v_____do__lift_3118_){
_start:
{
uint8_t v_pu_boxed_3119_; uint8_t v_t_boxed_3120_; lean_object* v_res_3121_; 
v_pu_boxed_3119_ = lean_unbox(v_pu_3110_);
v_t_boxed_3120_ = lean_unbox(v_t_3114_);
v_res_3121_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3119_, v_decl_3111_, v_inst_3112_, v_value_3113_, v_t_boxed_3120_, v_toPure_3115_, v_toBind_3116_, v_inst_3117_, v_____do__lift_3118_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3122_, uint8_t v_t_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_decl_3127_){
_start:
{
lean_object* v_toApplicative_3128_; lean_object* v_toBind_3129_; lean_object* v_type_3130_; lean_object* v_value_3131_; lean_object* v_toPure_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___f_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_toApplicative_3128_ = lean_ctor_get(v_inst_3125_, 0);
lean_inc_ref(v_toApplicative_3128_);
v_toBind_3129_ = lean_ctor_get(v_inst_3125_, 1);
lean_inc_n(v_toBind_3129_, 3);
lean_dec_ref(v_inst_3125_);
v_type_3130_ = lean_ctor_get(v_decl_3127_, 2);
lean_inc_ref(v_type_3130_);
v_value_3131_ = lean_ctor_get(v_decl_3127_, 3);
lean_inc(v_value_3131_);
v_toPure_3132_ = lean_ctor_get(v_toApplicative_3128_, 1);
lean_inc_n(v_toPure_3132_, 2);
lean_dec_ref(v_toApplicative_3128_);
v___x_3133_ = lean_box(v_pu_3122_);
v___x_3134_ = lean_box(v_t_3123_);
lean_inc(v_inst_3126_);
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3135_, 0, v___x_3133_);
lean_closure_set(v___f_3135_, 1, v_decl_3127_);
lean_closure_set(v___f_3135_, 2, v_inst_3124_);
lean_closure_set(v___f_3135_, 3, v_value_3131_);
lean_closure_set(v___f_3135_, 4, v___x_3134_);
lean_closure_set(v___f_3135_, 5, v_toPure_3132_);
lean_closure_set(v___f_3135_, 6, v_toBind_3129_);
lean_closure_set(v___f_3135_, 7, v_inst_3126_);
v___x_3136_ = lean_box(v_pu_3122_);
v___x_3137_ = lean_box(v_t_3123_);
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3138_, 0, v___x_3136_);
lean_closure_set(v___f_3138_, 1, v___x_3137_);
lean_closure_set(v___f_3138_, 2, v_type_3130_);
lean_closure_set(v___f_3138_, 3, v_toPure_3132_);
v___x_3139_ = lean_apply_4(v_toBind_3129_, lean_box(0), lean_box(0), v_inst_3126_, v___f_3138_);
v___x_3140_ = lean_apply_4(v_toBind_3129_, lean_box(0), lean_box(0), v___x_3139_, v___f_3135_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3141_, lean_object* v_t_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_decl_3146_){
_start:
{
uint8_t v_pu_boxed_3147_; uint8_t v_t_boxed_3148_; lean_object* v_res_3149_; 
v_pu_boxed_3147_ = lean_unbox(v_pu_3141_);
v_t_boxed_3148_ = lean_unbox(v_t_3142_);
v_res_3149_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3147_, v_t_boxed_3148_, v_inst_3143_, v_inst_3144_, v_inst_3145_, v_decl_3146_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3150_, uint8_t v_pu_3151_, uint8_t v_t_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_decl_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3151_, v_t_3152_, v_inst_3153_, v_inst_3154_, v_inst_3155_, v_decl_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3158_, lean_object* v_pu_3159_, lean_object* v_t_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_decl_3164_){
_start:
{
uint8_t v_pu_boxed_3165_; uint8_t v_t_boxed_3166_; lean_object* v_res_3167_; 
v_pu_boxed_3165_ = lean_unbox(v_pu_3159_);
v_t_boxed_3166_ = lean_unbox(v_t_3160_);
v_res_3167_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3158_, v_pu_boxed_3165_, v_t_boxed_3166_, v_inst_3161_, v_inst_3162_, v_inst_3163_, v_decl_3164_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg(){
_start:
{
lean_object* v___x_3169_; lean_object* v_toApplicative_3170_; lean_object* v_toFunctor_3171_; lean_object* v_toSeq_3172_; lean_object* v_toSeqLeft_3173_; lean_object* v_toSeqRight_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v_toApplicative_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3214_; 
v___x_3169_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3170_ = lean_ctor_get(v___x_3169_, 0);
v_toFunctor_3171_ = lean_ctor_get(v_toApplicative_3170_, 0);
v_toSeq_3172_ = lean_ctor_get(v_toApplicative_3170_, 2);
v_toSeqLeft_3173_ = lean_ctor_get(v_toApplicative_3170_, 3);
v_toSeqRight_3174_ = lean_ctor_get(v_toApplicative_3170_, 4);
v___f_3175_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3176_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3171_, 2);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toFunctor_3171_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toFunctor_3171_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___f_3177_);
lean_ctor_set(v___x_3179_, 1, v___f_3178_);
lean_inc(v_toSeqRight_3174_);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toSeqRight_3174_);
lean_inc(v_toSeqLeft_3173_);
v___f_3181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3181_, 0, v_toSeqLeft_3173_);
lean_inc(v_toSeq_3172_);
v___f_3182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3182_, 0, v_toSeq_3172_);
v___x_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3179_);
lean_ctor_set(v___x_3183_, 1, v___f_3175_);
lean_ctor_set(v___x_3183_, 2, v___f_3182_);
lean_ctor_set(v___x_3183_, 3, v___f_3181_);
lean_ctor_set(v___x_3183_, 4, v___f_3180_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___f_3176_);
v___x_3185_ = l_StateRefT_x27_instMonad___redArg(v___x_3184_);
v_toApplicative_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3185_, 1);
lean_dec(v_unused_3215_);
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3214_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_toApplicative_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3214_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_toFunctor_3190_; lean_object* v_toSeq_3191_; lean_object* v_toSeqLeft_3192_; lean_object* v_toSeqRight_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3212_; 
v_toFunctor_3190_ = lean_ctor_get(v_toApplicative_3186_, 0);
v_toSeq_3191_ = lean_ctor_get(v_toApplicative_3186_, 2);
v_toSeqLeft_3192_ = lean_ctor_get(v_toApplicative_3186_, 3);
v_toSeqRight_3193_ = lean_ctor_get(v_toApplicative_3186_, 4);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_toApplicative_3186_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_toApplicative_3186_, 1);
lean_dec(v_unused_3213_);
v___x_3195_ = v_toApplicative_3186_;
v_isShared_3196_ = v_isSharedCheck_3212_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_toSeqRight_3193_);
lean_inc(v_toSeqLeft_3192_);
lean_inc(v_toSeq_3191_);
lean_inc(v_toFunctor_3190_);
lean_dec(v_toApplicative_3186_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3212_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___f_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___x_3206_; 
v___f_3197_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3198_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3190_);
v___f_3199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3199_, 0, v_toFunctor_3190_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toFunctor_3190_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___f_3199_);
lean_ctor_set(v___x_3201_, 1, v___f_3200_);
v___f_3202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3202_, 0, v_toSeqRight_3193_);
v___f_3203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3203_, 0, v_toSeqLeft_3192_);
v___f_3204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3204_, 0, v_toSeq_3191_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 4, v___f_3202_);
lean_ctor_set(v___x_3195_, 3, v___f_3203_);
lean_ctor_set(v___x_3195_, 2, v___f_3204_);
lean_ctor_set(v___x_3195_, 1, v___f_3197_);
lean_ctor_set(v___x_3195_, 0, v___x_3201_);
v___x_3206_ = v___x_3195_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___f_3197_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v___f_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v___f_3203_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v___f_3202_);
v___x_3206_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v___f_3198_);
lean_ctor_set(v___x_3188_, 0, v___x_3206_);
v___x_3208_ = v___x_3188_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___f_3198_);
v___x_3208_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; 
v___x_3209_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3209_, 0, lean_box(0));
lean_closure_set(v___x_3209_, 1, lean_box(0));
lean_closure_set(v___x_3209_, 2, v___x_3208_);
return v___x_3209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object* v___dummy_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v_res_3217_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0(void){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3219_, uint8_t v_t_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0, &l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3222_, lean_object* v_t_3223_){
_start:
{
uint8_t v_pu_boxed_3224_; uint8_t v_t_boxed_3225_; lean_object* v_res_3226_; 
v_pu_boxed_3224_ = lean_unbox(v_pu_3222_);
v_t_boxed_3225_ = lean_unbox(v_t_3223_);
v_res_3226_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3224_, v_t_boxed_3225_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3227_, lean_object* v_inst_3228_, lean_object* v_result_3229_, lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_result_3229_) == 0)
{
lean_object* v_fvarId_3231_; lean_object* v___x_3232_; 
lean_dec(v_inst_3228_);
v_fvarId_3231_ = lean_ctor_get(v_result_3229_, 0);
lean_inc(v_fvarId_3231_);
lean_dec_ref_known(v_result_3229_, 1);
v___x_3232_ = lean_apply_1(v_x_3230_, v_fvarId_3231_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_dec(v_x_3230_);
v___x_3233_ = lean_box(v_pu_3227_);
v___x_3234_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3234_, 0, v___x_3233_);
v___x_3235_ = lean_apply_2(v_inst_3228_, lean_box(0), v___x_3234_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3236_, lean_object* v_inst_3237_, lean_object* v_result_3238_, lean_object* v_x_3239_){
_start:
{
uint8_t v_pu_boxed_3240_; lean_object* v_res_3241_; 
v_pu_boxed_3240_ = lean_unbox(v_pu_3236_);
v_res_3241_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3240_, v_inst_3237_, v_result_3238_, v_x_3239_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3242_, uint8_t v_pu_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_result_3246_, lean_object* v_x_3247_){
_start:
{
if (lean_obj_tag(v_result_3246_) == 0)
{
lean_object* v_fvarId_3248_; lean_object* v___x_3249_; 
lean_dec(v_inst_3244_);
v_fvarId_3248_ = lean_ctor_get(v_result_3246_, 0);
lean_inc(v_fvarId_3248_);
lean_dec_ref_known(v_result_3246_, 1);
v___x_3249_ = lean_apply_1(v_x_3247_, v_fvarId_3248_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v_x_3247_);
v___x_3250_ = lean_box(v_pu_3243_);
v___x_3251_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3251_, 0, v___x_3250_);
v___x_3252_ = lean_apply_2(v_inst_3244_, lean_box(0), v___x_3251_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3253_, lean_object* v_pu_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_result_3257_, lean_object* v_x_3258_){
_start:
{
uint8_t v_pu_boxed_3259_; lean_object* v_res_3260_; 
v_pu_boxed_3259_ = lean_unbox(v_pu_3254_);
v_res_3260_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3253_, v_pu_boxed_3259_, v_inst_3255_, v_inst_3256_, v_result_3257_, v_x_3258_);
lean_dec_ref(v_inst_3256_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3261_, uint8_t v_t_3262_, lean_object* v_args_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3261_, v___y_3264_, v_args_3263_, v_t_3262_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3268_, lean_object* v_t_3269_, lean_object* v_args_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_pu_boxed_3273_; uint8_t v_t_boxed_3274_; lean_object* v_res_3275_; 
v_pu_boxed_3273_ = lean_unbox(v_pu_3268_);
v_t_boxed_3274_ = lean_unbox(v_t_3269_);
v_res_3275_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3273_, v_t_boxed_3274_, v_args_3270_, v___y_3271_);
lean_dec_ref(v___y_3271_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3276_, uint8_t v_t_3277_, lean_object* v_i_3278_, lean_object* v_as_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = lean_array_get_size(v_as_3279_);
v___x_3284_ = lean_nat_dec_lt(v_i_3278_, v___x_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; 
lean_dec(v_i_3278_);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v_as_3279_);
return v___x_3285_;
}
else
{
lean_object* v_a_3286_; lean_object* v_type_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3286_ = lean_array_fget_borrowed(v_as_3279_, v_i_3278_);
v_type_3287_ = lean_ctor_get(v_a_3286_, 2);
lean_inc_ref(v_type_3287_);
v___x_3288_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3276_, v___y_3280_, v_t_3277_, v_type_3287_);
lean_inc(v_a_3286_);
v___x_3289_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3276_, v_a_3286_, v___x_3288_, v___y_3281_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; size_t v___x_3291_; size_t v___x_3292_; uint8_t v___x_3293_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3291_ = lean_ptr_addr(v_a_3286_);
v___x_3292_ = lean_ptr_addr(v_a_3290_);
v___x_3293_ = lean_usize_dec_eq(v___x_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_nat_add(v_i_3278_, v___x_3294_);
v___x_3296_ = lean_array_fset(v_as_3279_, v_i_3278_, v_a_3290_);
lean_dec(v_i_3278_);
v_i_3278_ = v___x_3295_;
v_as_3279_ = v___x_3296_;
goto _start;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_a_3290_);
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_nat_add(v_i_3278_, v___x_3298_);
lean_dec(v_i_3278_);
v_i_3278_ = v___x_3299_;
goto _start;
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_as_3279_);
lean_dec(v_i_3278_);
v_a_3301_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3289_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3289_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3309_, lean_object* v_t_3310_, lean_object* v_i_3311_, lean_object* v_as_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
uint8_t v_pu_boxed_3316_; uint8_t v_t_boxed_3317_; lean_object* v_res_3318_; 
v_pu_boxed_3316_ = lean_unbox(v_pu_3309_);
v_t_boxed_3317_ = lean_unbox(v_t_3310_);
v_res_3318_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3316_, v_t_boxed_3317_, v_i_3311_, v_as_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3319_, uint8_t v_t_3320_, lean_object* v_ps_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3319_, v_t_3320_, v___x_3328_, v_ps_3321_, v___y_3322_, v___y_3324_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3330_, lean_object* v_t_3331_, lean_object* v_ps_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
uint8_t v_pu_boxed_3339_; uint8_t v_t_boxed_3340_; lean_object* v_res_3341_; 
v_pu_boxed_3339_ = lean_unbox(v_pu_3330_);
v_t_boxed_3340_ = lean_unbox(v_t_3331_);
v_res_3341_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3339_, v_t_boxed_3340_, v_ps_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3342_, uint8_t v_t_3343_, lean_object* v_decl_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_type_3348_; lean_object* v_value_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_type_3348_ = lean_ctor_get(v_decl_3344_, 2);
v_value_3349_ = lean_ctor_get(v_decl_3344_, 3);
lean_inc_ref(v_type_3348_);
v___x_3350_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3342_, v___y_3345_, v_t_3343_, v_type_3348_);
lean_inc(v_value_3349_);
v___x_3351_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3342_, v___y_3345_, v_value_3349_, v_t_3343_);
v___x_3352_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3342_, v_decl_3344_, v___x_3350_, v___x_3351_, v___y_3346_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3353_, lean_object* v_t_3354_, lean_object* v_decl_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
uint8_t v_pu_boxed_3359_; uint8_t v_t_boxed_3360_; lean_object* v_res_3361_; 
v_pu_boxed_3359_ = lean_unbox(v_pu_3353_);
v_t_boxed_3360_ = lean_unbox(v_t_3354_);
v_res_3361_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3359_, v_t_boxed_3360_, v_decl_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3362_, uint8_t v_t_3363_, lean_object* v_i_3364_, lean_object* v_as_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = lean_array_get_size(v_as_3365_);
v___x_3373_ = lean_nat_dec_lt(v_i_3364_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
lean_dec(v_i_3364_);
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_as_3365_);
return v___x_3374_;
}
else
{
lean_object* v_a_3375_; lean_object* v_a_3377_; 
v_a_3375_ = lean_array_fget_borrowed(v_as_3365_, v_i_3364_);
switch(lean_obj_tag(v_a_3375_))
{
case 0:
{
lean_object* v_params_3388_; lean_object* v_code_3389_; lean_object* v___x_3390_; 
v_params_3388_ = lean_ctor_get(v_a_3375_, 1);
v_code_3389_ = lean_ctor_get(v_a_3375_, 2);
lean_inc_ref(v_params_3388_);
v___x_3390_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3362_, v_t_3363_, v_params_3388_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
lean_inc_ref(v_code_3389_);
v___x_3392_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3362_, v_t_3363_, v_code_3389_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
lean_inc_ref(v_a_3375_);
v___x_3394_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3362_, v_a_3375_, v_a_3391_, v_a_3393_);
v_a_3377_ = v___x_3394_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v_a_3391_);
lean_dec_ref(v_as_3365_);
lean_dec(v_i_3364_);
v_a_3395_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3392_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3392_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec_ref(v_as_3365_);
lean_dec(v_i_3364_);
v_a_3403_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3390_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3390_);
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
case 1:
{
lean_object* v_code_3411_; lean_object* v___x_3412_; 
v_code_3411_ = lean_ctor_get(v_a_3375_, 1);
lean_inc_ref(v_code_3411_);
v___x_3412_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3362_, v_t_3363_, v_code_3411_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
lean_inc_ref(v_a_3375_);
v___x_3414_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3375_, v_a_3413_);
v_a_3377_ = v___x_3414_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v_as_3365_);
lean_dec(v_i_3364_);
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
default: 
{
lean_object* v_code_3423_; lean_object* v___x_3424_; 
v_code_3423_ = lean_ctor_get(v_a_3375_, 0);
lean_inc_ref(v_code_3423_);
v___x_3424_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3362_, v_t_3363_, v_code_3423_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
lean_inc_ref(v_a_3375_);
v___x_3426_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3375_, v_a_3425_);
v_a_3377_ = v___x_3426_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v_as_3365_);
lean_dec(v_i_3364_);
v_a_3427_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3424_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3424_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
v___jp_3376_:
{
size_t v___x_3378_; size_t v___x_3379_; uint8_t v___x_3380_; 
v___x_3378_ = lean_ptr_addr(v_a_3375_);
v___x_3379_ = lean_ptr_addr(v_a_3377_);
v___x_3380_ = lean_usize_dec_eq(v___x_3378_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = lean_unsigned_to_nat(1u);
v___x_3382_ = lean_nat_add(v_i_3364_, v___x_3381_);
v___x_3383_ = lean_array_fset(v_as_3365_, v_i_3364_, v_a_3377_);
lean_dec(v_i_3364_);
v_i_3364_ = v___x_3382_;
v_as_3365_ = v___x_3383_;
goto _start;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec_ref(v_a_3377_);
v___x_3385_ = lean_unsigned_to_nat(1u);
v___x_3386_ = lean_nat_add(v_i_3364_, v___x_3385_);
lean_dec(v_i_3364_);
v_i_3364_ = v___x_3386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3435_, uint8_t v_t_3436_, lean_object* v_code_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
switch(lean_obj_tag(v_code_3437_))
{
case 0:
{
lean_object* v_decl_3444_; lean_object* v_k_3445_; lean_object* v___x_3446_; 
v_decl_3444_ = lean_ctor_get(v_code_3437_, 0);
v_k_3445_ = lean_ctor_get(v_code_3437_, 1);
lean_inc_ref(v_decl_3444_);
v___x_3446_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3435_, v_t_3436_, v_decl_3444_, v_a_3438_, v_a_3440_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
lean_inc_ref(v_k_3445_);
v___x_3448_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_3445_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3486_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3486_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3486_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
size_t v___x_3453_; size_t v___x_3454_; uint8_t v___x_3455_; 
v___x_3453_ = lean_ptr_addr(v_k_3445_);
v___x_3454_ = lean_ptr_addr(v_a_3449_);
v___x_3455_ = lean_usize_dec_eq(v___x_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3465_; 
v_isSharedCheck_3465_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; lean_object* v_unused_3467_; 
v_unused_3466_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3467_);
v___x_3457_ = v_code_3437_;
v_isShared_3458_ = v_isSharedCheck_3465_;
goto v_resetjp_3456_;
}
else
{
lean_dec(v_code_3437_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3465_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v_a_3449_);
lean_ctor_set(v___x_3457_, 0, v_a_3447_);
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3447_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_a_3449_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3460_);
v___x_3462_ = v___x_3451_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
size_t v___x_3468_; size_t v___x_3469_; uint8_t v___x_3470_; 
v___x_3468_ = lean_ptr_addr(v_decl_3444_);
v___x_3469_ = lean_ptr_addr(v_a_3447_);
v___x_3470_ = lean_usize_dec_eq(v___x_3468_, v___x_3469_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3480_; 
v_isSharedCheck_3480_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; lean_object* v_unused_3482_; 
v_unused_3481_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3481_);
v_unused_3482_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3482_);
v___x_3472_ = v_code_3437_;
v_isShared_3473_ = v_isSharedCheck_3480_;
goto v_resetjp_3471_;
}
else
{
lean_dec(v_code_3437_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3480_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v_a_3449_);
lean_ctor_set(v___x_3472_, 0, v_a_3447_);
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3447_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_a_3449_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3475_);
v___x_3477_ = v___x_3451_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
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
else
{
lean_object* v___x_3484_; 
lean_dec(v_a_3449_);
lean_dec(v_a_3447_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v_code_3437_);
v___x_3484_ = v___x_3451_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_code_3437_);
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
}
else
{
lean_dec(v_a_3447_);
lean_dec_ref_known(v_code_3437_, 2);
return v___x_3448_;
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref_known(v_code_3437_, 2);
v_a_3487_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3446_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3446_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
case 1:
{
lean_object* v_decl_3495_; lean_object* v_k_3496_; lean_object* v___x_3497_; 
v_decl_3495_ = lean_ctor_get(v_code_3437_, 0);
v_k_3496_ = lean_ctor_get(v_code_3437_, 1);
lean_inc_ref(v_decl_3495_);
v___x_3497_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3435_, v_t_3436_, v_decl_3495_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
lean_inc_ref(v_k_3496_);
v___x_3499_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_3496_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3537_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3537_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3537_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
size_t v___x_3504_; size_t v___x_3505_; uint8_t v___x_3506_; 
v___x_3504_ = lean_ptr_addr(v_k_3496_);
v___x_3505_ = lean_ptr_addr(v_a_3500_);
v___x_3506_ = lean_usize_dec_eq(v___x_3504_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3516_; 
v_isSharedCheck_3516_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; lean_object* v_unused_3518_; 
v_unused_3517_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3517_);
v_unused_3518_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3518_);
v___x_3508_ = v_code_3437_;
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v_code_3437_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v_a_3500_);
lean_ctor_set(v___x_3508_, 0, v_a_3498_);
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3498_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_a_3500_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3511_);
v___x_3513_ = v___x_3502_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
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
else
{
size_t v___x_3519_; size_t v___x_3520_; uint8_t v___x_3521_; 
v___x_3519_ = lean_ptr_addr(v_decl_3495_);
v___x_3520_ = lean_ptr_addr(v_a_3498_);
v___x_3521_ = lean_usize_dec_eq(v___x_3519_, v___x_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3531_; 
v_isSharedCheck_3531_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; lean_object* v_unused_3533_; 
v_unused_3532_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3533_);
v___x_3523_ = v_code_3437_;
v_isShared_3524_ = v_isSharedCheck_3531_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v_code_3437_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3531_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 1, v_a_3500_);
lean_ctor_set(v___x_3523_, 0, v_a_3498_);
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3498_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_a_3500_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3526_);
v___x_3528_ = v___x_3502_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
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
else
{
lean_object* v___x_3535_; 
lean_dec(v_a_3500_);
lean_dec(v_a_3498_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v_code_3437_);
v___x_3535_ = v___x_3502_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_code_3437_);
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
}
else
{
lean_dec(v_a_3498_);
lean_dec_ref_known(v_code_3437_, 2);
return v___x_3499_;
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec_ref_known(v_code_3437_, 2);
v_a_3538_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3497_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3497_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
case 2:
{
lean_object* v_decl_3546_; lean_object* v_k_3547_; lean_object* v___x_3548_; 
v_decl_3546_ = lean_ctor_get(v_code_3437_, 0);
v_k_3547_ = lean_ctor_get(v_code_3437_, 1);
lean_inc_ref(v_decl_3546_);
v___x_3548_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3435_, v_t_3436_, v_decl_3546_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
lean_inc_ref(v_k_3547_);
v___x_3550_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_3547_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3588_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3588_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3588_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
size_t v___x_3555_; size_t v___x_3556_; uint8_t v___x_3557_; 
v___x_3555_ = lean_ptr_addr(v_k_3547_);
v___x_3556_ = lean_ptr_addr(v_a_3551_);
v___x_3557_ = lean_usize_dec_eq(v___x_3555_, v___x_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3567_; 
v_isSharedCheck_3567_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; lean_object* v_unused_3569_; 
v_unused_3568_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3569_);
v___x_3559_ = v_code_3437_;
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
else
{
lean_dec(v_code_3437_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v_a_3551_);
lean_ctor_set(v___x_3559_, 0, v_a_3549_);
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3549_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_a_3551_);
v___x_3562_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3562_);
v___x_3564_ = v___x_3553_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
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
else
{
size_t v___x_3570_; size_t v___x_3571_; uint8_t v___x_3572_; 
v___x_3570_ = lean_ptr_addr(v_decl_3546_);
v___x_3571_ = lean_ptr_addr(v_a_3549_);
v___x_3572_ = lean_usize_dec_eq(v___x_3570_, v___x_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3582_; 
v_isSharedCheck_3582_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3582_ == 0)
{
lean_object* v_unused_3583_; lean_object* v_unused_3584_; 
v_unused_3583_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3583_);
v_unused_3584_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3584_);
v___x_3574_ = v_code_3437_;
v_isShared_3575_ = v_isSharedCheck_3582_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v_code_3437_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3582_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v_a_3551_);
lean_ctor_set(v___x_3574_, 0, v_a_3549_);
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3549_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_a_3551_);
v___x_3577_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3579_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3577_);
v___x_3579_ = v___x_3553_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v___x_3586_; 
lean_dec(v_a_3551_);
lean_dec(v_a_3549_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v_code_3437_);
v___x_3586_ = v___x_3553_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_code_3437_);
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
}
else
{
lean_dec(v_a_3549_);
lean_dec_ref_known(v_code_3437_, 2);
return v___x_3550_;
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref_known(v_code_3437_, 2);
v_a_3589_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3548_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3548_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3597_; lean_object* v_args_3598_; lean_object* v___x_3599_; 
v_fvarId_3597_ = lean_ctor_get(v_code_3437_, 0);
v_args_3598_ = lean_ctor_get(v_code_3437_, 1);
lean_inc(v_fvarId_3597_);
v___x_3599_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_3597_, v_t_3436_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_fvarId_3600_; lean_object* v___x_3601_; 
v_fvarId_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_fvarId_3600_);
lean_dec_ref_known(v___x_3599_, 1);
lean_inc_ref(v_args_3598_);
v___x_3601_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3435_, v_t_3436_, v_args_3598_, v_a_3438_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3627_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3627_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3627_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
uint8_t v___y_3607_; uint8_t v___x_3623_; 
v___x_3623_ = l_Lean_instBEqFVarId_beq(v_fvarId_3597_, v_fvarId_3600_);
if (v___x_3623_ == 0)
{
v___y_3607_ = v___x_3623_;
goto v___jp_3606_;
}
else
{
size_t v___x_3624_; size_t v___x_3625_; uint8_t v___x_3626_; 
v___x_3624_ = lean_ptr_addr(v_args_3598_);
v___x_3625_ = lean_ptr_addr(v_a_3602_);
v___x_3626_ = lean_usize_dec_eq(v___x_3624_, v___x_3625_);
v___y_3607_ = v___x_3626_;
goto v___jp_3606_;
}
v___jp_3606_:
{
if (v___y_3607_ == 0)
{
lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3617_; 
v_isSharedCheck_3617_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; lean_object* v_unused_3619_; 
v_unused_3618_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3618_);
v_unused_3619_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3619_);
v___x_3609_ = v_code_3437_;
v_isShared_3610_ = v_isSharedCheck_3617_;
goto v_resetjp_3608_;
}
else
{
lean_dec(v_code_3437_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3617_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v_a_3602_);
lean_ctor_set(v___x_3609_, 0, v_fvarId_3600_);
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_fvarId_3600_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_a_3602_);
v___x_3612_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3612_);
v___x_3614_ = v___x_3604_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v___x_3621_; 
lean_dec(v_a_3602_);
lean_dec(v_fvarId_3600_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v_code_3437_);
v___x_3621_ = v___x_3604_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_code_3437_);
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
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_fvarId_3600_);
lean_dec_ref_known(v_code_3437_, 2);
v_a_3628_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3601_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3601_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_object* v___x_3636_; 
lean_dec_ref_known(v_code_3437_, 2);
v___x_3636_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3636_;
}
}
case 4:
{
lean_object* v_cases_3637_; lean_object* v_typeName_3638_; lean_object* v_resultType_3639_; lean_object* v_discr_3640_; lean_object* v_alts_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3686_; 
v_cases_3637_ = lean_ctor_get(v_code_3437_, 0);
lean_inc_ref(v_cases_3637_);
v_typeName_3638_ = lean_ctor_get(v_cases_3637_, 0);
v_resultType_3639_ = lean_ctor_get(v_cases_3637_, 1);
v_discr_3640_ = lean_ctor_get(v_cases_3637_, 2);
v_alts_3641_ = lean_ctor_get(v_cases_3637_, 3);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_cases_3637_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3643_ = v_cases_3637_;
v_isShared_3644_ = v_isSharedCheck_3686_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_alts_3641_);
lean_inc(v_discr_3640_);
lean_inc(v_resultType_3639_);
lean_inc(v_typeName_3638_);
lean_dec(v_cases_3637_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3686_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_inc_ref(v_resultType_3639_);
v___x_3645_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3435_, v_a_3438_, v_t_3436_, v_resultType_3639_);
lean_inc(v_discr_3640_);
v___x_3646_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_discr_3640_, v_t_3436_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_fvarId_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3684_; 
v_fvarId_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3684_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_fvarId_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3684_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3641_);
v___x_3652_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3435_, v_t_3436_, v___x_3651_, v_alts_3641_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3675_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3675_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3675_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
size_t v___x_3667_; size_t v___x_3668_; uint8_t v___x_3669_; 
v___x_3667_ = lean_ptr_addr(v_alts_3641_);
lean_dec_ref(v_alts_3641_);
v___x_3668_ = lean_ptr_addr(v_a_3653_);
v___x_3669_ = lean_usize_dec_eq(v___x_3667_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_dec(v_discr_3640_);
lean_dec_ref(v_resultType_3639_);
lean_dec_ref_known(v_code_3437_, 1);
goto v___jp_3657_;
}
else
{
size_t v___x_3670_; size_t v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = lean_ptr_addr(v_resultType_3639_);
lean_dec_ref(v_resultType_3639_);
v___x_3671_ = lean_ptr_addr(v___x_3645_);
v___x_3672_ = lean_usize_dec_eq(v___x_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_dec(v_discr_3640_);
lean_dec_ref_known(v_code_3437_, 1);
goto v___jp_3657_;
}
else
{
uint8_t v___x_3673_; 
v___x_3673_ = l_Lean_instBEqFVarId_beq(v_discr_3640_, v_fvarId_3647_);
lean_dec(v_discr_3640_);
if (v___x_3673_ == 0)
{
lean_dec_ref_known(v_code_3437_, 1);
goto v___jp_3657_;
}
else
{
lean_object* v___x_3674_; 
lean_del_object(v___x_3655_);
lean_dec(v_a_3653_);
lean_del_object(v___x_3649_);
lean_dec(v_fvarId_3647_);
lean_dec_ref(v___x_3645_);
lean_del_object(v___x_3643_);
lean_dec(v_typeName_3638_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v_code_3437_);
return v___x_3674_;
}
}
}
v___jp_3657_:
{
lean_object* v___x_3659_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 3, v_a_3653_);
lean_ctor_set(v___x_3643_, 2, v_fvarId_3647_);
lean_ctor_set(v___x_3643_, 1, v___x_3645_);
v___x_3659_ = v___x_3643_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_typeName_3638_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_fvarId_3647_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_a_3653_);
v___x_3659_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 4);
lean_ctor_set(v___x_3649_, 0, v___x_3659_);
v___x_3661_ = v___x_3649_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3661_);
v___x_3663_ = v___x_3655_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_del_object(v___x_3649_);
lean_dec(v_fvarId_3647_);
lean_dec_ref(v___x_3645_);
lean_del_object(v___x_3643_);
lean_dec_ref(v_alts_3641_);
lean_dec(v_discr_3640_);
lean_dec_ref(v_resultType_3639_);
lean_dec(v_typeName_3638_);
lean_dec_ref_known(v_code_3437_, 1);
v_a_3676_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3652_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3652_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
else
{
lean_object* v___x_3685_; 
lean_dec_ref(v___x_3645_);
lean_del_object(v___x_3643_);
lean_dec_ref(v_alts_3641_);
lean_dec(v_discr_3640_);
lean_dec_ref(v_resultType_3639_);
lean_dec(v_typeName_3638_);
lean_dec_ref_known(v_code_3437_, 1);
v___x_3685_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3685_;
}
}
}
case 5:
{
lean_object* v_fvarId_3687_; lean_object* v___x_3688_; 
v_fvarId_3687_ = lean_ctor_get(v_code_3437_, 0);
lean_inc(v_fvarId_3687_);
v___x_3688_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_3687_, v_t_3436_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_fvarId_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3708_; 
v_fvarId_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3708_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_fvarId_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3708_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
uint8_t v___x_3693_; 
v___x_3693_ = l_Lean_instBEqFVarId_beq(v_fvarId_3687_, v_fvarId_3689_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3703_; 
v_isSharedCheck_3703_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; 
v_unused_3704_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3704_);
v___x_3695_ = v_code_3437_;
v_isShared_3696_ = v_isSharedCheck_3703_;
goto v_resetjp_3694_;
}
else
{
lean_dec(v_code_3437_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3703_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v_fvarId_3689_);
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_fvarId_3689_);
v___x_3698_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3700_; 
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3698_);
v___x_3700_ = v___x_3691_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
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
else
{
lean_object* v___x_3706_; 
lean_dec(v_fvarId_3689_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v_code_3437_);
v___x_3706_ = v___x_3691_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_code_3437_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v___x_3709_; 
lean_dec_ref_known(v_code_3437_, 1);
v___x_3709_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3709_;
}
}
case 6:
{
lean_object* v_type_3710_; lean_object* v___x_3711_; size_t v___x_3712_; size_t v___x_3713_; uint8_t v___x_3714_; 
v_type_3710_ = lean_ctor_get(v_code_3437_, 0);
lean_inc_ref(v_type_3710_);
v___x_3711_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3435_, v_a_3438_, v_t_3436_, v_type_3710_);
v___x_3712_ = lean_ptr_addr(v_type_3710_);
v___x_3713_ = lean_ptr_addr(v___x_3711_);
v___x_3714_ = lean_usize_dec_eq(v___x_3712_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3722_; 
v_isSharedCheck_3722_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; 
v_unused_3723_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3723_);
v___x_3716_ = v_code_3437_;
v_isShared_3717_ = v_isSharedCheck_3722_;
goto v_resetjp_3715_;
}
else
{
lean_dec(v_code_3437_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3722_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3711_);
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3711_);
v___x_3719_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
}
}
else
{
lean_object* v___x_3724_; 
lean_dec_ref(v___x_3711_);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v_code_3437_);
return v___x_3724_;
}
}
case 7:
{
lean_object* v_fvarId_3725_; lean_object* v_i_3726_; lean_object* v_y_3727_; lean_object* v_k_3728_; lean_object* v___x_3729_; 
v_fvarId_3725_ = lean_ctor_get(v_code_3437_, 0);
v_i_3726_ = lean_ctor_get(v_code_3437_, 1);
v_y_3727_ = lean_ctor_get(v_code_3437_, 2);
v_k_3728_ = lean_ctor_get(v_code_3437_, 3);
lean_inc(v_fvarId_3725_);
v___x_3729_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_3725_, v_t_3436_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_fvarId_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_fvarId_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_fvarId_3730_);
lean_dec_ref_known(v___x_3729_, 1);
lean_inc(v_y_3727_);
v___x_3731_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3435_, v_a_3438_, v_y_3727_, v_t_3436_);
lean_inc_ref(v_k_3728_);
v___x_3732_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_3728_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3806_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3806_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3806_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
size_t v___x_3737_; size_t v___x_3738_; uint8_t v___x_3739_; 
v___x_3737_ = lean_ptr_addr(v_fvarId_3725_);
v___x_3738_ = lean_ptr_addr(v_fvarId_3730_);
v___x_3739_ = lean_usize_dec_eq(v___x_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3749_; 
lean_inc(v_i_3726_);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; 
v_unused_3750_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3753_);
v___x_3741_ = v_code_3437_;
v_isShared_3742_ = v_isSharedCheck_3749_;
goto v_resetjp_3740_;
}
else
{
lean_dec(v_code_3437_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3749_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 3, v_a_3733_);
lean_ctor_set(v___x_3741_, 2, v___x_3731_);
lean_ctor_set(v___x_3741_, 0, v_fvarId_3730_);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_fvarId_3730_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_i_3726_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3748_, 3, v_a_3733_);
v___x_3744_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3746_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3744_);
v___x_3746_ = v___x_3735_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_nat_dec_eq(v_i_3726_, v_i_3726_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3764_; 
lean_inc(v_i_3726_);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; 
v_unused_3765_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3768_);
v___x_3756_ = v_code_3437_;
v_isShared_3757_ = v_isSharedCheck_3764_;
goto v_resetjp_3755_;
}
else
{
lean_dec(v_code_3437_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3764_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 3, v_a_3733_);
lean_ctor_set(v___x_3756_, 2, v___x_3731_);
lean_ctor_set(v___x_3756_, 0, v_fvarId_3730_);
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_fvarId_3730_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_i_3726_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_a_3733_);
v___x_3759_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3761_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3759_);
v___x_3761_ = v___x_3735_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
size_t v___x_3769_; size_t v___x_3770_; uint8_t v___x_3771_; 
v___x_3769_ = lean_ptr_addr(v_y_3727_);
v___x_3770_ = lean_ptr_addr(v___x_3731_);
v___x_3771_ = lean_usize_dec_eq(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3781_; 
lean_inc(v_i_3726_);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; lean_object* v_unused_3783_; lean_object* v_unused_3784_; lean_object* v_unused_3785_; 
v_unused_3782_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3785_);
v___x_3773_ = v_code_3437_;
v_isShared_3774_ = v_isSharedCheck_3781_;
goto v_resetjp_3772_;
}
else
{
lean_dec(v_code_3437_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3781_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 3, v_a_3733_);
lean_ctor_set(v___x_3773_, 2, v___x_3731_);
lean_ctor_set(v___x_3773_, 0, v_fvarId_3730_);
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_fvarId_3730_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_i_3726_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_a_3733_);
v___x_3776_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3776_);
v___x_3778_ = v___x_3735_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
size_t v___x_3786_; size_t v___x_3787_; uint8_t v___x_3788_; 
v___x_3786_ = lean_ptr_addr(v_k_3728_);
v___x_3787_ = lean_ptr_addr(v_a_3733_);
v___x_3788_ = lean_usize_dec_eq(v___x_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3798_; 
lean_inc(v_i_3726_);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3798_ == 0)
{
lean_object* v_unused_3799_; lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; 
v_unused_3799_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3802_);
v___x_3790_ = v_code_3437_;
v_isShared_3791_ = v_isSharedCheck_3798_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v_code_3437_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3798_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 3, v_a_3733_);
lean_ctor_set(v___x_3790_, 2, v___x_3731_);
lean_ctor_set(v___x_3790_, 0, v_fvarId_3730_);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_fvarId_3730_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_i_3726_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_a_3733_);
v___x_3793_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3795_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3793_);
v___x_3795_ = v___x_3735_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v___x_3804_; 
lean_dec(v_a_3733_);
lean_dec(v___x_3731_);
lean_dec(v_fvarId_3730_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v_code_3437_);
v___x_3804_ = v___x_3735_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_code_3437_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3731_);
lean_dec(v_fvarId_3730_);
lean_dec_ref_known(v_code_3437_, 4);
return v___x_3732_;
}
}
else
{
lean_object* v___x_3807_; 
lean_dec_ref_known(v_code_3437_, 4);
v___x_3807_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3807_;
}
}
case 8:
{
lean_object* v_fvarId_3808_; lean_object* v_i_3809_; lean_object* v_y_3810_; lean_object* v_k_3811_; lean_object* v___x_3812_; 
v_fvarId_3808_ = lean_ctor_get(v_code_3437_, 0);
v_i_3809_ = lean_ctor_get(v_code_3437_, 1);
v_y_3810_ = lean_ctor_get(v_code_3437_, 2);
v_k_3811_ = lean_ctor_get(v_code_3437_, 3);
lean_inc(v_fvarId_3808_);
v___x_3812_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_3808_, v_t_3436_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_fvarId_3813_; lean_object* v___x_3814_; 
v_fvarId_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_fvarId_3813_);
lean_dec_ref_known(v___x_3812_, 1);
lean_inc(v_y_3810_);
v___x_3814_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_y_3810_, v_t_3436_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_fvarId_3815_; lean_object* v___x_3816_; 
v_fvarId_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_fvarId_3815_);
lean_dec_ref_known(v___x_3814_, 1);
lean_inc_ref(v_k_3811_);
v___x_3816_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_3811_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3890_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3890_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3890_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
size_t v___x_3821_; size_t v___x_3822_; uint8_t v___x_3823_; 
v___x_3821_ = lean_ptr_addr(v_fvarId_3808_);
v___x_3822_ = lean_ptr_addr(v_fvarId_3813_);
v___x_3823_ = lean_usize_dec_eq(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3833_; 
lean_inc(v_i_3809_);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; 
v_unused_3834_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3837_);
v___x_3825_ = v_code_3437_;
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v_code_3437_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 3, v_a_3817_);
lean_ctor_set(v___x_3825_, 2, v_fvarId_3815_);
lean_ctor_set(v___x_3825_, 0, v_fvarId_3813_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_fvarId_3813_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_i_3809_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_fvarId_3815_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_a_3817_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3828_);
v___x_3830_ = v___x_3819_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_nat_dec_eq(v_i_3809_, v_i_3809_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3848_; 
lean_inc(v_i_3809_);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; lean_object* v_unused_3852_; 
v_unused_3849_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3852_);
v___x_3840_ = v_code_3437_;
v_isShared_3841_ = v_isSharedCheck_3848_;
goto v_resetjp_3839_;
}
else
{
lean_dec(v_code_3437_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3848_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 3, v_a_3817_);
lean_ctor_set(v___x_3840_, 2, v_fvarId_3815_);
lean_ctor_set(v___x_3840_, 0, v_fvarId_3813_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_fvarId_3813_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_i_3809_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_fvarId_3815_);
lean_ctor_set(v_reuseFailAlloc_3847_, 3, v_a_3817_);
v___x_3843_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3845_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3843_);
v___x_3845_ = v___x_3819_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
else
{
size_t v___x_3853_; size_t v___x_3854_; uint8_t v___x_3855_; 
v___x_3853_ = lean_ptr_addr(v_y_3810_);
v___x_3854_ = lean_ptr_addr(v_fvarId_3815_);
v___x_3855_ = lean_usize_dec_eq(v___x_3853_, v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3865_; 
lean_inc(v_i_3809_);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; lean_object* v_unused_3867_; lean_object* v_unused_3868_; lean_object* v_unused_3869_; 
v_unused_3866_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3869_);
v___x_3857_ = v_code_3437_;
v_isShared_3858_ = v_isSharedCheck_3865_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_code_3437_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3865_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 3, v_a_3817_);
lean_ctor_set(v___x_3857_, 2, v_fvarId_3815_);
lean_ctor_set(v___x_3857_, 0, v_fvarId_3813_);
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_fvarId_3813_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_i_3809_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_fvarId_3815_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_a_3817_);
v___x_3860_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3862_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3860_);
v___x_3862_ = v___x_3819_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
size_t v___x_3870_; size_t v___x_3871_; uint8_t v___x_3872_; 
v___x_3870_ = lean_ptr_addr(v_k_3811_);
v___x_3871_ = lean_ptr_addr(v_a_3817_);
v___x_3872_ = lean_usize_dec_eq(v___x_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3882_; 
lean_inc(v_i_3809_);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; 
v_unused_3883_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3886_);
v___x_3874_ = v_code_3437_;
v_isShared_3875_ = v_isSharedCheck_3882_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v_code_3437_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3882_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 3, v_a_3817_);
lean_ctor_set(v___x_3874_, 2, v_fvarId_3815_);
lean_ctor_set(v___x_3874_, 0, v_fvarId_3813_);
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_fvarId_3813_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_i_3809_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_fvarId_3815_);
lean_ctor_set(v_reuseFailAlloc_3881_, 3, v_a_3817_);
v___x_3877_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3879_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3877_);
v___x_3879_ = v___x_3819_;
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
lean_object* v___x_3888_; 
lean_dec(v_a_3817_);
lean_dec(v_fvarId_3815_);
lean_dec(v_fvarId_3813_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v_code_3437_);
v___x_3888_ = v___x_3819_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_code_3437_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3815_);
lean_dec(v_fvarId_3813_);
lean_dec_ref_known(v_code_3437_, 4);
return v___x_3816_;
}
}
else
{
lean_object* v___x_3891_; 
lean_dec(v_fvarId_3813_);
lean_dec_ref_known(v_code_3437_, 4);
v___x_3891_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3891_;
}
}
else
{
lean_object* v___x_3892_; 
lean_dec_ref_known(v_code_3437_, 4);
v___x_3892_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3892_;
}
}
case 9:
{
lean_object* v_fvarId_3893_; lean_object* v_i_3894_; lean_object* v_offset_3895_; lean_object* v_y_3896_; lean_object* v_ty_3897_; lean_object* v_k_3898_; lean_object* v___x_3899_; 
v_fvarId_3893_ = lean_ctor_get(v_code_3437_, 0);
v_i_3894_ = lean_ctor_get(v_code_3437_, 1);
v_offset_3895_ = lean_ctor_get(v_code_3437_, 2);
v_y_3896_ = lean_ctor_get(v_code_3437_, 3);
v_ty_3897_ = lean_ctor_get(v_code_3437_, 4);
v_k_3898_ = lean_ctor_get(v_code_3437_, 5);
lean_inc(v_fvarId_3893_);
v___x_3899_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_3893_, v_t_3436_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_fvarId_3900_; lean_object* v___x_3901_; 
v_fvarId_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_fvarId_3900_);
lean_dec_ref_known(v___x_3899_, 1);
lean_inc(v_y_3896_);
v___x_3901_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_y_3896_, v_t_3436_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_fvarId_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_fvarId_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_fvarId_3902_);
lean_dec_ref_known(v___x_3901_, 1);
lean_inc_ref(v_ty_3897_);
v___x_3903_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3435_, v_a_3438_, v_t_3436_, v_ty_3897_);
lean_inc_ref(v_k_3898_);
v___x_3904_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_3898_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_4022_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_4022_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_4022_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
size_t v___x_3909_; size_t v___x_3910_; uint8_t v___x_3911_; 
v___x_3909_ = lean_ptr_addr(v_fvarId_3893_);
v___x_3910_ = lean_ptr_addr(v_fvarId_3900_);
v___x_3911_ = lean_usize_dec_eq(v___x_3909_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3921_; 
lean_inc(v_offset_3895_);
lean_inc(v_i_3894_);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; lean_object* v_unused_3925_; lean_object* v_unused_3926_; lean_object* v_unused_3927_; 
v_unused_3922_ = lean_ctor_get(v_code_3437_, 5);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_code_3437_, 4);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3927_);
v___x_3913_ = v_code_3437_;
v_isShared_3914_ = v_isSharedCheck_3921_;
goto v_resetjp_3912_;
}
else
{
lean_dec(v_code_3437_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3921_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 5, v_a_3905_);
lean_ctor_set(v___x_3913_, 4, v___x_3903_);
lean_ctor_set(v___x_3913_, 3, v_fvarId_3902_);
lean_ctor_set(v___x_3913_, 0, v_fvarId_3900_);
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_fvarId_3900_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_i_3894_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_offset_3895_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v_fvarId_3902_);
lean_ctor_set(v_reuseFailAlloc_3920_, 4, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3920_, 5, v_a_3905_);
v___x_3916_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3918_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3916_);
v___x_3918_ = v___x_3907_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_nat_dec_eq(v_i_3894_, v_i_3894_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3938_; 
lean_inc(v_offset_3895_);
lean_inc(v_i_3894_);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; lean_object* v_unused_3944_; 
v_unused_3939_ = lean_ctor_get(v_code_3437_, 5);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_code_3437_, 4);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3944_);
v___x_3930_ = v_code_3437_;
v_isShared_3931_ = v_isSharedCheck_3938_;
goto v_resetjp_3929_;
}
else
{
lean_dec(v_code_3437_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3938_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 5, v_a_3905_);
lean_ctor_set(v___x_3930_, 4, v___x_3903_);
lean_ctor_set(v___x_3930_, 3, v_fvarId_3902_);
lean_ctor_set(v___x_3930_, 0, v_fvarId_3900_);
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_fvarId_3900_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_i_3894_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_offset_3895_);
lean_ctor_set(v_reuseFailAlloc_3937_, 3, v_fvarId_3902_);
lean_ctor_set(v_reuseFailAlloc_3937_, 4, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3937_, 5, v_a_3905_);
v___x_3933_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3935_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3933_);
v___x_3935_ = v___x_3907_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
else
{
uint8_t v___x_3945_; 
v___x_3945_ = lean_nat_dec_eq(v_offset_3895_, v_offset_3895_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3955_; 
lean_inc(v_offset_3895_);
lean_inc(v_i_3894_);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; lean_object* v_unused_3961_; 
v_unused_3956_ = lean_ctor_get(v_code_3437_, 5);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_code_3437_, 4);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3961_);
v___x_3947_ = v_code_3437_;
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
else
{
lean_dec(v_code_3437_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 5, v_a_3905_);
lean_ctor_set(v___x_3947_, 4, v___x_3903_);
lean_ctor_set(v___x_3947_, 3, v_fvarId_3902_);
lean_ctor_set(v___x_3947_, 0, v_fvarId_3900_);
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_fvarId_3900_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_i_3894_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_offset_3895_);
lean_ctor_set(v_reuseFailAlloc_3954_, 3, v_fvarId_3902_);
lean_ctor_set(v_reuseFailAlloc_3954_, 4, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3954_, 5, v_a_3905_);
v___x_3950_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3950_);
v___x_3952_ = v___x_3907_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
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
else
{
size_t v___x_3962_; size_t v___x_3963_; uint8_t v___x_3964_; 
v___x_3962_ = lean_ptr_addr(v_y_3896_);
v___x_3963_ = lean_ptr_addr(v_fvarId_3902_);
v___x_3964_ = lean_usize_dec_eq(v___x_3962_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3974_; 
lean_inc(v_offset_3895_);
lean_inc(v_i_3894_);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; lean_object* v_unused_3976_; lean_object* v_unused_3977_; lean_object* v_unused_3978_; lean_object* v_unused_3979_; lean_object* v_unused_3980_; 
v_unused_3975_ = lean_ctor_get(v_code_3437_, 5);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_code_3437_, 4);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3980_);
v___x_3966_ = v_code_3437_;
v_isShared_3967_ = v_isSharedCheck_3974_;
goto v_resetjp_3965_;
}
else
{
lean_dec(v_code_3437_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3974_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 5, v_a_3905_);
lean_ctor_set(v___x_3966_, 4, v___x_3903_);
lean_ctor_set(v___x_3966_, 3, v_fvarId_3902_);
lean_ctor_set(v___x_3966_, 0, v_fvarId_3900_);
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_fvarId_3900_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_i_3894_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_offset_3895_);
lean_ctor_set(v_reuseFailAlloc_3973_, 3, v_fvarId_3902_);
lean_ctor_set(v_reuseFailAlloc_3973_, 4, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3973_, 5, v_a_3905_);
v___x_3969_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3971_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3969_);
v___x_3971_ = v___x_3907_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3969_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
size_t v___x_3981_; size_t v___x_3982_; uint8_t v___x_3983_; 
v___x_3981_ = lean_ptr_addr(v_ty_3897_);
v___x_3982_ = lean_ptr_addr(v___x_3903_);
v___x_3983_ = lean_usize_dec_eq(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3993_; 
lean_inc(v_offset_3895_);
lean_inc(v_i_3894_);
v_isSharedCheck_3993_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_3993_ == 0)
{
lean_object* v_unused_3994_; lean_object* v_unused_3995_; lean_object* v_unused_3996_; lean_object* v_unused_3997_; lean_object* v_unused_3998_; lean_object* v_unused_3999_; 
v_unused_3994_ = lean_ctor_get(v_code_3437_, 5);
lean_dec(v_unused_3994_);
v_unused_3995_ = lean_ctor_get(v_code_3437_, 4);
lean_dec(v_unused_3995_);
v_unused_3996_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_3997_);
v_unused_3998_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_3998_);
v_unused_3999_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_3999_);
v___x_3985_ = v_code_3437_;
v_isShared_3986_ = v_isSharedCheck_3993_;
goto v_resetjp_3984_;
}
else
{
lean_dec(v_code_3437_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3993_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 5, v_a_3905_);
lean_ctor_set(v___x_3985_, 4, v___x_3903_);
lean_ctor_set(v___x_3985_, 3, v_fvarId_3902_);
lean_ctor_set(v___x_3985_, 0, v_fvarId_3900_);
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_fvarId_3900_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_i_3894_);
lean_ctor_set(v_reuseFailAlloc_3992_, 2, v_offset_3895_);
lean_ctor_set(v_reuseFailAlloc_3992_, 3, v_fvarId_3902_);
lean_ctor_set(v_reuseFailAlloc_3992_, 4, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3992_, 5, v_a_3905_);
v___x_3988_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3990_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3988_);
v___x_3990_ = v___x_3907_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
size_t v___x_4000_; size_t v___x_4001_; uint8_t v___x_4002_; 
v___x_4000_ = lean_ptr_addr(v_k_3898_);
v___x_4001_ = lean_ptr_addr(v_a_3905_);
v___x_4002_ = lean_usize_dec_eq(v___x_4000_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4012_; 
lean_inc(v_offset_3895_);
lean_inc(v_i_3894_);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; lean_object* v_unused_4017_; lean_object* v_unused_4018_; 
v_unused_4013_ = lean_ctor_get(v_code_3437_, 5);
lean_dec(v_unused_4013_);
v_unused_4014_ = lean_ctor_get(v_code_3437_, 4);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4016_);
v_unused_4017_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4017_);
v_unused_4018_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4018_);
v___x_4004_ = v_code_3437_;
v_isShared_4005_ = v_isSharedCheck_4012_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v_code_3437_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4012_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 5, v_a_3905_);
lean_ctor_set(v___x_4004_, 4, v___x_3903_);
lean_ctor_set(v___x_4004_, 3, v_fvarId_3902_);
lean_ctor_set(v___x_4004_, 0, v_fvarId_3900_);
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_fvarId_3900_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_i_3894_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_offset_3895_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v_fvarId_3902_);
lean_ctor_set(v_reuseFailAlloc_4011_, 4, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_4011_, 5, v_a_3905_);
v___x_4007_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_4007_);
v___x_4009_ = v___x_3907_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
else
{
lean_object* v___x_4020_; 
lean_dec(v_a_3905_);
lean_dec_ref(v___x_3903_);
lean_dec(v_fvarId_3902_);
lean_dec(v_fvarId_3900_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v_code_3437_);
v___x_4020_ = v___x_3907_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_code_3437_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
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
lean_dec_ref(v___x_3903_);
lean_dec(v_fvarId_3902_);
lean_dec(v_fvarId_3900_);
lean_dec_ref_known(v_code_3437_, 6);
return v___x_3904_;
}
}
else
{
lean_object* v___x_4023_; 
lean_dec(v_fvarId_3900_);
lean_dec_ref_known(v_code_3437_, 6);
v___x_4023_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_4023_;
}
}
else
{
lean_object* v___x_4024_; 
lean_dec_ref_known(v_code_3437_, 6);
v___x_4024_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_4024_;
}
}
case 10:
{
lean_object* v_fvarId_4025_; lean_object* v_cidx_4026_; lean_object* v_k_4027_; lean_object* v___x_4028_; 
v_fvarId_4025_ = lean_ctor_get(v_code_3437_, 0);
v_cidx_4026_ = lean_ctor_get(v_code_3437_, 1);
v_k_4027_ = lean_ctor_get(v_code_3437_, 2);
lean_inc(v_fvarId_4025_);
v___x_4028_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_4025_, v_t_3436_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_fvarId_4029_; lean_object* v___x_4030_; 
v_fvarId_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_fvarId_4029_);
lean_dec_ref_known(v___x_4028_, 1);
lean_inc_ref(v_k_4027_);
v___x_4030_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_4027_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4084_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4084_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4084_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
size_t v___x_4035_; size_t v___x_4036_; uint8_t v___x_4037_; 
v___x_4035_ = lean_ptr_addr(v_fvarId_4025_);
v___x_4036_ = lean_ptr_addr(v_fvarId_4029_);
v___x_4037_ = lean_usize_dec_eq(v___x_4035_, v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4047_; 
lean_inc(v_cidx_4026_);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; lean_object* v_unused_4049_; lean_object* v_unused_4050_; 
v_unused_4048_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4048_);
v_unused_4049_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4049_);
v_unused_4050_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4050_);
v___x_4039_ = v_code_3437_;
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
else
{
lean_dec(v_code_3437_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 2, v_a_4031_);
lean_ctor_set(v___x_4039_, 0, v_fvarId_4029_);
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_fvarId_4029_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_cidx_4026_);
lean_ctor_set(v_reuseFailAlloc_4046_, 2, v_a_4031_);
v___x_4042_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4042_);
v___x_4044_ = v___x_4033_;
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
uint8_t v___x_4051_; 
v___x_4051_ = lean_nat_dec_eq(v_cidx_4026_, v_cidx_4026_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4061_; 
lean_inc(v_cidx_4026_);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4061_ == 0)
{
lean_object* v_unused_4062_; lean_object* v_unused_4063_; lean_object* v_unused_4064_; 
v_unused_4062_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4064_);
v___x_4053_ = v_code_3437_;
v_isShared_4054_ = v_isSharedCheck_4061_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v_code_3437_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4061_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 2, v_a_4031_);
lean_ctor_set(v___x_4053_, 0, v_fvarId_4029_);
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_fvarId_4029_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_cidx_4026_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_a_4031_);
v___x_4056_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4058_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4056_);
v___x_4058_ = v___x_4033_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4056_);
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
else
{
size_t v___x_4065_; size_t v___x_4066_; uint8_t v___x_4067_; 
v___x_4065_ = lean_ptr_addr(v_k_4027_);
v___x_4066_ = lean_ptr_addr(v_a_4031_);
v___x_4067_ = lean_usize_dec_eq(v___x_4065_, v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4077_; 
lean_inc(v_cidx_4026_);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4077_ == 0)
{
lean_object* v_unused_4078_; lean_object* v_unused_4079_; lean_object* v_unused_4080_; 
v_unused_4078_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4079_);
v_unused_4080_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4080_);
v___x_4069_ = v_code_3437_;
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_code_3437_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 2, v_a_4031_);
lean_ctor_set(v___x_4069_, 0, v_fvarId_4029_);
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fvarId_4029_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_cidx_4026_);
lean_ctor_set(v_reuseFailAlloc_4076_, 2, v_a_4031_);
v___x_4072_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4072_);
v___x_4074_ = v___x_4033_;
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
lean_object* v___x_4082_; 
lean_dec(v_a_4031_);
lean_dec(v_fvarId_4029_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v_code_3437_);
v___x_4082_ = v___x_4033_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_code_3437_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4029_);
lean_dec_ref_known(v_code_3437_, 3);
return v___x_4030_;
}
}
else
{
lean_object* v___x_4085_; 
lean_dec_ref_known(v_code_3437_, 3);
v___x_4085_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_4085_;
}
}
case 11:
{
lean_object* v_fvarId_4086_; lean_object* v_n_4087_; uint8_t v_check_4088_; uint8_t v_persistent_4089_; lean_object* v_k_4090_; lean_object* v___x_4091_; 
v_fvarId_4086_ = lean_ctor_get(v_code_3437_, 0);
v_n_4087_ = lean_ctor_get(v_code_3437_, 1);
v_check_4088_ = lean_ctor_get_uint8(v_code_3437_, sizeof(void*)*3);
v_persistent_4089_ = lean_ctor_get_uint8(v_code_3437_, sizeof(void*)*3 + 1);
v_k_4090_ = lean_ctor_get(v_code_3437_, 2);
lean_inc(v_fvarId_4086_);
v___x_4091_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_4086_, v_t_3436_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_fvarId_4092_; lean_object* v___x_4093_; 
v_fvarId_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_fvarId_4092_);
lean_dec_ref_known(v___x_4091_, 1);
lean_inc_ref(v_k_4090_);
v___x_4093_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_4090_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4147_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4096_ = v___x_4093_;
v_isShared_4097_ = v_isSharedCheck_4147_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4147_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
size_t v___x_4098_; size_t v___x_4099_; uint8_t v___x_4100_; 
v___x_4098_ = lean_ptr_addr(v_fvarId_4086_);
v___x_4099_ = lean_ptr_addr(v_fvarId_4092_);
v___x_4100_ = lean_usize_dec_eq(v___x_4098_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4110_; 
lean_inc(v_n_4087_);
v_isSharedCheck_4110_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4110_ == 0)
{
lean_object* v_unused_4111_; lean_object* v_unused_4112_; lean_object* v_unused_4113_; 
v_unused_4111_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4111_);
v_unused_4112_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4112_);
v_unused_4113_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4113_);
v___x_4102_ = v_code_3437_;
v_isShared_4103_ = v_isSharedCheck_4110_;
goto v_resetjp_4101_;
}
else
{
lean_dec(v_code_3437_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4110_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 2, v_a_4094_);
lean_ctor_set(v___x_4102_, 0, v_fvarId_4092_);
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_fvarId_4092_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_n_4087_);
lean_ctor_set(v_reuseFailAlloc_4109_, 2, v_a_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4109_, sizeof(void*)*3, v_check_4088_);
lean_ctor_set_uint8(v_reuseFailAlloc_4109_, sizeof(void*)*3 + 1, v_persistent_4089_);
v___x_4105_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4107_; 
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4105_);
v___x_4107_ = v___x_4096_;
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
uint8_t v___x_4114_; 
v___x_4114_ = lean_nat_dec_eq(v_n_4087_, v_n_4087_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4124_; 
lean_inc(v_n_4087_);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4124_ == 0)
{
lean_object* v_unused_4125_; lean_object* v_unused_4126_; lean_object* v_unused_4127_; 
v_unused_4125_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4125_);
v_unused_4126_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4126_);
v_unused_4127_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4127_);
v___x_4116_ = v_code_3437_;
v_isShared_4117_ = v_isSharedCheck_4124_;
goto v_resetjp_4115_;
}
else
{
lean_dec(v_code_3437_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4124_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 2, v_a_4094_);
lean_ctor_set(v___x_4116_, 0, v_fvarId_4092_);
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_fvarId_4092_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v_n_4087_);
lean_ctor_set(v_reuseFailAlloc_4123_, 2, v_a_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4123_, sizeof(void*)*3, v_check_4088_);
lean_ctor_set_uint8(v_reuseFailAlloc_4123_, sizeof(void*)*3 + 1, v_persistent_4089_);
v___x_4119_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
lean_object* v___x_4121_; 
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4119_);
v___x_4121_ = v___x_4096_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4119_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
size_t v___x_4128_; size_t v___x_4129_; uint8_t v___x_4130_; 
v___x_4128_ = lean_ptr_addr(v_k_4090_);
v___x_4129_ = lean_ptr_addr(v_a_4094_);
v___x_4130_ = lean_usize_dec_eq(v___x_4128_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4140_; 
lean_inc(v_n_4087_);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; lean_object* v_unused_4142_; lean_object* v_unused_4143_; 
v_unused_4141_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4141_);
v_unused_4142_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4143_);
v___x_4132_ = v_code_3437_;
v_isShared_4133_ = v_isSharedCheck_4140_;
goto v_resetjp_4131_;
}
else
{
lean_dec(v_code_3437_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4140_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 2, v_a_4094_);
lean_ctor_set(v___x_4132_, 0, v_fvarId_4092_);
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_fvarId_4092_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_n_4087_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_a_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4139_, sizeof(void*)*3, v_check_4088_);
lean_ctor_set_uint8(v_reuseFailAlloc_4139_, sizeof(void*)*3 + 1, v_persistent_4089_);
v___x_4135_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4137_; 
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4135_);
v___x_4137_ = v___x_4096_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
else
{
lean_object* v___x_4145_; 
lean_dec(v_a_4094_);
lean_dec(v_fvarId_4092_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v_code_3437_);
v___x_4145_ = v___x_4096_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_code_3437_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4092_);
lean_dec_ref_known(v_code_3437_, 3);
return v___x_4093_;
}
}
else
{
lean_object* v___x_4148_; 
lean_dec_ref_known(v_code_3437_, 3);
v___x_4148_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_4148_;
}
}
case 12:
{
lean_object* v_fvarId_4149_; lean_object* v_n_4150_; uint8_t v_check_4151_; uint8_t v_persistent_4152_; lean_object* v_objs_x3f_4153_; lean_object* v_k_4154_; lean_object* v___x_4155_; 
v_fvarId_4149_ = lean_ctor_get(v_code_3437_, 0);
v_n_4150_ = lean_ctor_get(v_code_3437_, 1);
v_check_4151_ = lean_ctor_get_uint8(v_code_3437_, sizeof(void*)*4);
v_persistent_4152_ = lean_ctor_get_uint8(v_code_3437_, sizeof(void*)*4 + 1);
v_objs_x3f_4153_ = lean_ctor_get(v_code_3437_, 2);
v_k_4154_ = lean_ctor_get(v_code_3437_, 3);
lean_inc(v_fvarId_4149_);
v___x_4155_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_4149_, v_t_3436_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_fvarId_4156_; lean_object* v___x_4157_; 
v_fvarId_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_fvarId_4156_);
lean_dec_ref_known(v___x_4155_, 1);
lean_inc_ref(v_k_4154_);
v___x_4157_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_4154_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4230_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4230_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4230_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
size_t v___x_4162_; size_t v___x_4163_; uint8_t v___x_4164_; 
v___x_4162_ = lean_ptr_addr(v_fvarId_4149_);
v___x_4163_ = lean_ptr_addr(v_fvarId_4156_);
v___x_4164_ = lean_usize_dec_eq(v___x_4162_, v___x_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4174_; 
lean_inc(v_objs_x3f_4153_);
lean_inc(v_n_4150_);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4174_ == 0)
{
lean_object* v_unused_4175_; lean_object* v_unused_4176_; lean_object* v_unused_4177_; lean_object* v_unused_4178_; 
v_unused_4175_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_4175_);
v_unused_4176_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4176_);
v_unused_4177_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4178_);
v___x_4166_ = v_code_3437_;
v_isShared_4167_ = v_isSharedCheck_4174_;
goto v_resetjp_4165_;
}
else
{
lean_dec(v_code_3437_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4174_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 3, v_a_4158_);
lean_ctor_set(v___x_4166_, 0, v_fvarId_4156_);
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_fvarId_4156_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_n_4150_);
lean_ctor_set(v_reuseFailAlloc_4173_, 2, v_objs_x3f_4153_);
lean_ctor_set(v_reuseFailAlloc_4173_, 3, v_a_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4173_, sizeof(void*)*4, v_check_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4173_, sizeof(void*)*4 + 1, v_persistent_4152_);
v___x_4169_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4171_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4169_);
v___x_4171_ = v___x_4160_;
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
uint8_t v___x_4179_; 
v___x_4179_ = lean_nat_dec_eq(v_n_4150_, v_n_4150_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4189_; 
lean_inc(v_objs_x3f_4153_);
lean_inc(v_n_4150_);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4189_ == 0)
{
lean_object* v_unused_4190_; lean_object* v_unused_4191_; lean_object* v_unused_4192_; lean_object* v_unused_4193_; 
v_unused_4190_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_4190_);
v_unused_4191_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4191_);
v_unused_4192_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4193_);
v___x_4181_ = v_code_3437_;
v_isShared_4182_ = v_isSharedCheck_4189_;
goto v_resetjp_4180_;
}
else
{
lean_dec(v_code_3437_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4189_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 3, v_a_4158_);
lean_ctor_set(v___x_4181_, 0, v_fvarId_4156_);
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_fvarId_4156_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_n_4150_);
lean_ctor_set(v_reuseFailAlloc_4188_, 2, v_objs_x3f_4153_);
lean_ctor_set(v_reuseFailAlloc_4188_, 3, v_a_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4188_, sizeof(void*)*4, v_check_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4188_, sizeof(void*)*4 + 1, v_persistent_4152_);
v___x_4184_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4186_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4184_);
v___x_4186_ = v___x_4160_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
else
{
size_t v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = lean_ptr_addr(v_objs_x3f_4153_);
v___x_4195_ = lean_usize_dec_eq(v___x_4194_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4205_; 
lean_inc(v_objs_x3f_4153_);
lean_inc(v_n_4150_);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4205_ == 0)
{
lean_object* v_unused_4206_; lean_object* v_unused_4207_; lean_object* v_unused_4208_; lean_object* v_unused_4209_; 
v_unused_4206_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_4206_);
v_unused_4207_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4207_);
v_unused_4208_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4208_);
v_unused_4209_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4209_);
v___x_4197_ = v_code_3437_;
v_isShared_4198_ = v_isSharedCheck_4205_;
goto v_resetjp_4196_;
}
else
{
lean_dec(v_code_3437_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4205_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 3, v_a_4158_);
lean_ctor_set(v___x_4197_, 0, v_fvarId_4156_);
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_fvarId_4156_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v_n_4150_);
lean_ctor_set(v_reuseFailAlloc_4204_, 2, v_objs_x3f_4153_);
lean_ctor_set(v_reuseFailAlloc_4204_, 3, v_a_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, sizeof(void*)*4, v_check_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, sizeof(void*)*4 + 1, v_persistent_4152_);
v___x_4200_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4202_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4200_);
v___x_4202_ = v___x_4160_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
else
{
size_t v___x_4210_; size_t v___x_4211_; uint8_t v___x_4212_; 
v___x_4210_ = lean_ptr_addr(v_k_4154_);
v___x_4211_ = lean_ptr_addr(v_a_4158_);
v___x_4212_ = lean_usize_dec_eq(v___x_4210_, v___x_4211_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4222_; 
lean_inc(v_objs_x3f_4153_);
lean_inc(v_n_4150_);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4222_ == 0)
{
lean_object* v_unused_4223_; lean_object* v_unused_4224_; lean_object* v_unused_4225_; lean_object* v_unused_4226_; 
v_unused_4223_ = lean_ctor_get(v_code_3437_, 3);
lean_dec(v_unused_4223_);
v_unused_4224_ = lean_ctor_get(v_code_3437_, 2);
lean_dec(v_unused_4224_);
v_unused_4225_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4225_);
v_unused_4226_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4226_);
v___x_4214_ = v_code_3437_;
v_isShared_4215_ = v_isSharedCheck_4222_;
goto v_resetjp_4213_;
}
else
{
lean_dec(v_code_3437_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4222_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 3, v_a_4158_);
lean_ctor_set(v___x_4214_, 0, v_fvarId_4156_);
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_fvarId_4156_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_n_4150_);
lean_ctor_set(v_reuseFailAlloc_4221_, 2, v_objs_x3f_4153_);
lean_ctor_set(v_reuseFailAlloc_4221_, 3, v_a_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*4, v_check_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*4 + 1, v_persistent_4152_);
v___x_4217_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4219_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4217_);
v___x_4219_ = v___x_4160_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v___x_4228_; 
lean_dec(v_a_4158_);
lean_dec(v_fvarId_4156_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v_code_3437_);
v___x_4228_ = v___x_4160_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_code_3437_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4156_);
lean_dec_ref_known(v_code_3437_, 4);
return v___x_4157_;
}
}
else
{
lean_object* v___x_4231_; 
lean_dec_ref_known(v_code_3437_, 4);
v___x_4231_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_4231_;
}
}
default: 
{
lean_object* v_fvarId_4232_; lean_object* v_k_4233_; lean_object* v___x_4234_; 
v_fvarId_4232_ = lean_ctor_get(v_code_3437_, 0);
v_k_4233_ = lean_ctor_get(v_code_3437_, 1);
lean_inc(v_fvarId_4232_);
v___x_4234_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3438_, v_fvarId_4232_, v_t_3436_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_fvarId_4235_; lean_object* v___x_4236_; 
v_fvarId_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_fvarId_4235_);
lean_dec_ref_known(v___x_4234_, 1);
lean_inc_ref(v_k_4233_);
v___x_4236_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3435_, v_t_3436_, v_k_4233_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4274_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4274_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4274_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
size_t v___x_4241_; size_t v___x_4242_; uint8_t v___x_4243_; 
v___x_4241_ = lean_ptr_addr(v_fvarId_4232_);
v___x_4242_ = lean_ptr_addr(v_fvarId_4235_);
v___x_4243_ = lean_usize_dec_eq(v___x_4241_, v___x_4242_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4253_; 
v_isSharedCheck_4253_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; lean_object* v_unused_4255_; 
v_unused_4254_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4254_);
v_unused_4255_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4255_);
v___x_4245_ = v_code_3437_;
v_isShared_4246_ = v_isSharedCheck_4253_;
goto v_resetjp_4244_;
}
else
{
lean_dec(v_code_3437_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4253_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 1, v_a_4237_);
lean_ctor_set(v___x_4245_, 0, v_fvarId_4235_);
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_fvarId_4235_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_a_4237_);
v___x_4248_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4250_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4248_);
v___x_4250_ = v___x_4239_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
size_t v___x_4256_; size_t v___x_4257_; uint8_t v___x_4258_; 
v___x_4256_ = lean_ptr_addr(v_k_4233_);
v___x_4257_ = lean_ptr_addr(v_a_4237_);
v___x_4258_ = lean_usize_dec_eq(v___x_4256_, v___x_4257_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4268_; 
v_isSharedCheck_4268_ = !lean_is_exclusive(v_code_3437_);
if (v_isSharedCheck_4268_ == 0)
{
lean_object* v_unused_4269_; lean_object* v_unused_4270_; 
v_unused_4269_ = lean_ctor_get(v_code_3437_, 1);
lean_dec(v_unused_4269_);
v_unused_4270_ = lean_ctor_get(v_code_3437_, 0);
lean_dec(v_unused_4270_);
v___x_4260_ = v_code_3437_;
v_isShared_4261_ = v_isSharedCheck_4268_;
goto v_resetjp_4259_;
}
else
{
lean_dec(v_code_3437_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4268_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 1, v_a_4237_);
lean_ctor_set(v___x_4260_, 0, v_fvarId_4235_);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_fvarId_4235_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_a_4237_);
v___x_4263_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4265_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4263_);
v___x_4265_ = v___x_4239_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_object* v___x_4272_; 
lean_dec(v_a_4237_);
lean_dec(v_fvarId_4235_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v_code_3437_);
v___x_4272_ = v___x_4239_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_code_3437_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4235_);
lean_dec_ref_known(v_code_3437_, 2);
return v___x_4236_;
}
}
else
{
lean_object* v___x_4275_; 
lean_dec_ref_known(v_code_3437_, 2);
v___x_4275_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_4275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4276_, uint8_t v_t_4277_, lean_object* v_decl_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_params_4285_; lean_object* v_type_4286_; lean_object* v_value_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_params_4285_ = lean_ctor_get(v_decl_4278_, 2);
v_type_4286_ = lean_ctor_get(v_decl_4278_, 3);
v_value_4287_ = lean_ctor_get(v_decl_4278_, 4);
lean_inc_ref(v_type_4286_);
v___x_4288_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4276_, v_a_4279_, v_t_4277_, v_type_4286_);
lean_inc_ref(v_params_4285_);
v___x_4289_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4276_, v_t_4277_, v_params_4285_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4291_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4289_, 1);
lean_inc_ref(v_value_4287_);
v___x_4291_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4276_, v_t_4277_, v_value_4287_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4276_, v_decl_4278_, v___x_4288_, v_a_4290_, v_a_4292_, v_a_4281_);
return v___x_4293_;
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec(v_a_4290_);
lean_dec_ref(v___x_4288_);
lean_dec_ref(v_decl_4278_);
v_a_4294_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4291_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4291_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec_ref(v___x_4288_);
lean_dec_ref(v_decl_4278_);
v_a_4302_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4289_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4289_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4310_, lean_object* v_t_4311_, lean_object* v_decl_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_){
_start:
{
uint8_t v_pu_boxed_4319_; uint8_t v_t_boxed_4320_; lean_object* v_res_4321_; 
v_pu_boxed_4319_ = lean_unbox(v_pu_4310_);
v_t_boxed_4320_ = lean_unbox(v_t_4311_);
v_res_4321_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4319_, v_t_boxed_4320_, v_decl_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec_ref(v_a_4313_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4322_, lean_object* v_t_4323_, lean_object* v_i_4324_, lean_object* v_as_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
uint8_t v_pu_boxed_4332_; uint8_t v_t_boxed_4333_; lean_object* v_res_4334_; 
v_pu_boxed_4332_ = lean_unbox(v_pu_4322_);
v_t_boxed_4333_ = lean_unbox(v_t_4323_);
v_res_4334_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4332_, v_t_boxed_4333_, v_i_4324_, v_as_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec_ref(v___y_4326_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4335_, lean_object* v_t_4336_, lean_object* v_code_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_){
_start:
{
uint8_t v_pu_boxed_4344_; uint8_t v_t_boxed_4345_; lean_object* v_res_4346_; 
v_pu_boxed_4344_ = lean_unbox(v_pu_4335_);
v_t_boxed_4345_ = lean_unbox(v_t_4336_);
v_res_4346_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4344_, v_t_boxed_4345_, v_code_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
lean_dec_ref(v_a_4338_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4347_, uint8_t v_t_4348_, uint8_t v_pu_4349_, uint8_t v_t_4350_, lean_object* v_decl_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4349_, v_t_4350_, v_decl_4351_, v___y_4352_, v___y_4354_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4359_, lean_object* v_t_4360_, lean_object* v_pu_4361_, lean_object* v_t_4362_, lean_object* v_decl_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
uint8_t v_pu_boxed_4370_; uint8_t v_t_boxed_4371_; uint8_t v_pu_boxed_4372_; uint8_t v_t_boxed_4373_; lean_object* v_res_4374_; 
v_pu_boxed_4370_ = lean_unbox(v_pu_4359_);
v_t_boxed_4371_ = lean_unbox(v_t_4360_);
v_pu_boxed_4372_ = lean_unbox(v_pu_4361_);
v_t_boxed_4373_ = lean_unbox(v_t_4362_);
v_res_4374_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4370_, v_t_boxed_4371_, v_pu_boxed_4372_, v_t_boxed_4373_, v_decl_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec_ref(v___y_4364_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4375_, uint8_t v_t_4376_, uint8_t v_pu_4377_, uint8_t v_t_4378_, lean_object* v_args_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4377_, v_t_4378_, v_args_4379_, v___y_4380_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4387_, lean_object* v_t_4388_, lean_object* v_pu_4389_, lean_object* v_t_4390_, lean_object* v_args_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
uint8_t v_pu_boxed_4398_; uint8_t v_t_boxed_4399_; uint8_t v_pu_boxed_4400_; uint8_t v_t_boxed_4401_; lean_object* v_res_4402_; 
v_pu_boxed_4398_ = lean_unbox(v_pu_4387_);
v_t_boxed_4399_ = lean_unbox(v_t_4388_);
v_pu_boxed_4400_ = lean_unbox(v_pu_4389_);
v_t_boxed_4401_ = lean_unbox(v_t_4390_);
v_res_4402_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4398_, v_t_boxed_4399_, v_pu_boxed_4400_, v_t_boxed_4401_, v_args_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec_ref(v___y_4392_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4403_, uint8_t v_t_4404_, uint8_t v_pu_4405_, uint8_t v_t_4406_, lean_object* v_ps_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4405_, v_t_4406_, v_ps_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4415_, lean_object* v_t_4416_, lean_object* v_pu_4417_, lean_object* v_t_4418_, lean_object* v_ps_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
uint8_t v_pu_boxed_4426_; uint8_t v_t_boxed_4427_; uint8_t v_pu_boxed_4428_; uint8_t v_t_boxed_4429_; lean_object* v_res_4430_; 
v_pu_boxed_4426_ = lean_unbox(v_pu_4415_);
v_t_boxed_4427_ = lean_unbox(v_t_4416_);
v_pu_boxed_4428_ = lean_unbox(v_pu_4417_);
v_t_boxed_4429_ = lean_unbox(v_t_4418_);
v_res_4430_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4426_, v_t_boxed_4427_, v_pu_boxed_4428_, v_t_boxed_4429_, v_ps_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec_ref(v___y_4420_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4431_, uint8_t v_t_4432_, lean_object* v_i_4433_, lean_object* v_as_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4431_, v_t_4432_, v_i_4433_, v_as_4434_, v___y_4435_, v___y_4437_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4442_, lean_object* v_t_4443_, lean_object* v_i_4444_, lean_object* v_as_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
uint8_t v_pu_boxed_4452_; uint8_t v_t_boxed_4453_; lean_object* v_res_4454_; 
v_pu_boxed_4452_ = lean_unbox(v_pu_4442_);
v_t_boxed_4453_ = lean_unbox(v_t_4443_);
v_res_4454_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4452_, v_t_boxed_4453_, v_i_4444_, v_as_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4455_, uint8_t v_t_4456_, lean_object* v_decl_4457_, lean_object* v_inst_4458_, lean_object* v_____do__lift_4459_){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4460_ = lean_box(v_pu_4455_);
v___x_4461_ = lean_box(v_t_4456_);
v___x_4462_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4462_, 0, v___x_4460_);
lean_closure_set(v___x_4462_, 1, v___x_4461_);
lean_closure_set(v___x_4462_, 2, v_decl_4457_);
lean_closure_set(v___x_4462_, 3, v_____do__lift_4459_);
v___x_4463_ = lean_apply_2(v_inst_4458_, lean_box(0), v___x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4464_, lean_object* v_t_4465_, lean_object* v_decl_4466_, lean_object* v_inst_4467_, lean_object* v_____do__lift_4468_){
_start:
{
uint8_t v_pu_boxed_4469_; uint8_t v_t_boxed_4470_; lean_object* v_res_4471_; 
v_pu_boxed_4469_ = lean_unbox(v_pu_4464_);
v_t_boxed_4470_ = lean_unbox(v_t_4465_);
v_res_4471_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4469_, v_t_boxed_4470_, v_decl_4466_, v_inst_4467_, v_____do__lift_4468_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4472_, uint8_t v_t_4473_, lean_object* v_inst_4474_, lean_object* v_inst_4475_, lean_object* v_inst_4476_, lean_object* v_decl_4477_){
_start:
{
lean_object* v_toBind_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___f_4481_; lean_object* v___x_4482_; 
v_toBind_4478_ = lean_ctor_get(v_inst_4475_, 1);
lean_inc(v_toBind_4478_);
lean_dec_ref(v_inst_4475_);
v___x_4479_ = lean_box(v_pu_4472_);
v___x_4480_ = lean_box(v_t_4473_);
v___f_4481_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4481_, 0, v___x_4479_);
lean_closure_set(v___f_4481_, 1, v___x_4480_);
lean_closure_set(v___f_4481_, 2, v_decl_4477_);
lean_closure_set(v___f_4481_, 3, v_inst_4474_);
v___x_4482_ = lean_apply_4(v_toBind_4478_, lean_box(0), lean_box(0), v_inst_4476_, v___f_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4483_, lean_object* v_t_4484_, lean_object* v_inst_4485_, lean_object* v_inst_4486_, lean_object* v_inst_4487_, lean_object* v_decl_4488_){
_start:
{
uint8_t v_pu_boxed_4489_; uint8_t v_t_boxed_4490_; lean_object* v_res_4491_; 
v_pu_boxed_4489_ = lean_unbox(v_pu_4483_);
v_t_boxed_4490_ = lean_unbox(v_t_4484_);
v_res_4491_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4489_, v_t_boxed_4490_, v_inst_4485_, v_inst_4486_, v_inst_4487_, v_decl_4488_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4492_, uint8_t v_pu_4493_, uint8_t v_t_4494_, lean_object* v_inst_4495_, lean_object* v_inst_4496_, lean_object* v_inst_4497_, lean_object* v_decl_4498_){
_start:
{
lean_object* v_toBind_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; 
v_toBind_4499_ = lean_ctor_get(v_inst_4496_, 1);
lean_inc(v_toBind_4499_);
lean_dec_ref(v_inst_4496_);
v___x_4500_ = lean_box(v_pu_4493_);
v___x_4501_ = lean_box(v_t_4494_);
v___f_4502_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4502_, 0, v___x_4500_);
lean_closure_set(v___f_4502_, 1, v___x_4501_);
lean_closure_set(v___f_4502_, 2, v_decl_4498_);
lean_closure_set(v___f_4502_, 3, v_inst_4495_);
v___x_4503_ = lean_apply_4(v_toBind_4499_, lean_box(0), lean_box(0), v_inst_4497_, v___f_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4504_, lean_object* v_pu_4505_, lean_object* v_t_4506_, lean_object* v_inst_4507_, lean_object* v_inst_4508_, lean_object* v_inst_4509_, lean_object* v_decl_4510_){
_start:
{
uint8_t v_pu_boxed_4511_; uint8_t v_t_boxed_4512_; lean_object* v_res_4513_; 
v_pu_boxed_4511_ = lean_unbox(v_pu_4505_);
v_t_boxed_4512_ = lean_unbox(v_t_4506_);
v_res_4513_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4504_, v_pu_boxed_4511_, v_t_boxed_4512_, v_inst_4507_, v_inst_4508_, v_inst_4509_, v_decl_4510_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4514_, uint8_t v_t_4515_, lean_object* v_code_4516_, lean_object* v_inst_4517_, lean_object* v_____do__lift_4518_){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4519_ = lean_box(v_pu_4514_);
v___x_4520_ = lean_box(v_t_4515_);
v___x_4521_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4521_, 0, v___x_4519_);
lean_closure_set(v___x_4521_, 1, v___x_4520_);
lean_closure_set(v___x_4521_, 2, v_code_4516_);
lean_closure_set(v___x_4521_, 3, v_____do__lift_4518_);
v___x_4522_ = lean_apply_2(v_inst_4517_, lean_box(0), v___x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4523_, lean_object* v_t_4524_, lean_object* v_code_4525_, lean_object* v_inst_4526_, lean_object* v_____do__lift_4527_){
_start:
{
uint8_t v_pu_boxed_4528_; uint8_t v_t_boxed_4529_; lean_object* v_res_4530_; 
v_pu_boxed_4528_ = lean_unbox(v_pu_4523_);
v_t_boxed_4529_ = lean_unbox(v_t_4524_);
v_res_4530_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4528_, v_t_boxed_4529_, v_code_4525_, v_inst_4526_, v_____do__lift_4527_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4531_, uint8_t v_t_4532_, lean_object* v_inst_4533_, lean_object* v_inst_4534_, lean_object* v_inst_4535_, lean_object* v_code_4536_){
_start:
{
lean_object* v_toBind_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___f_4540_; lean_object* v___x_4541_; 
v_toBind_4537_ = lean_ctor_get(v_inst_4534_, 1);
lean_inc(v_toBind_4537_);
lean_dec_ref(v_inst_4534_);
v___x_4538_ = lean_box(v_pu_4531_);
v___x_4539_ = lean_box(v_t_4532_);
v___f_4540_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4540_, 0, v___x_4538_);
lean_closure_set(v___f_4540_, 1, v___x_4539_);
lean_closure_set(v___f_4540_, 2, v_code_4536_);
lean_closure_set(v___f_4540_, 3, v_inst_4533_);
v___x_4541_ = lean_apply_4(v_toBind_4537_, lean_box(0), lean_box(0), v_inst_4535_, v___f_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4542_, lean_object* v_t_4543_, lean_object* v_inst_4544_, lean_object* v_inst_4545_, lean_object* v_inst_4546_, lean_object* v_code_4547_){
_start:
{
uint8_t v_pu_boxed_4548_; uint8_t v_t_boxed_4549_; lean_object* v_res_4550_; 
v_pu_boxed_4548_ = lean_unbox(v_pu_4542_);
v_t_boxed_4549_ = lean_unbox(v_t_4543_);
v_res_4550_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4548_, v_t_boxed_4549_, v_inst_4544_, v_inst_4545_, v_inst_4546_, v_code_4547_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4551_, uint8_t v_pu_4552_, uint8_t v_t_4553_, lean_object* v_inst_4554_, lean_object* v_inst_4555_, lean_object* v_inst_4556_, lean_object* v_code_4557_){
_start:
{
lean_object* v_toBind_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___f_4561_; lean_object* v___x_4562_; 
v_toBind_4558_ = lean_ctor_get(v_inst_4555_, 1);
lean_inc(v_toBind_4558_);
lean_dec_ref(v_inst_4555_);
v___x_4559_ = lean_box(v_pu_4552_);
v___x_4560_ = lean_box(v_t_4553_);
v___f_4561_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4561_, 0, v___x_4559_);
lean_closure_set(v___f_4561_, 1, v___x_4560_);
lean_closure_set(v___f_4561_, 2, v_code_4557_);
lean_closure_set(v___f_4561_, 3, v_inst_4554_);
v___x_4562_ = lean_apply_4(v_toBind_4558_, lean_box(0), lean_box(0), v_inst_4556_, v___f_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4563_, lean_object* v_pu_4564_, lean_object* v_t_4565_, lean_object* v_inst_4566_, lean_object* v_inst_4567_, lean_object* v_inst_4568_, lean_object* v_code_4569_){
_start:
{
uint8_t v_pu_boxed_4570_; uint8_t v_t_boxed_4571_; lean_object* v_res_4572_; 
v_pu_boxed_4570_ = lean_unbox(v_pu_4564_);
v_t_boxed_4571_ = lean_unbox(v_t_4565_);
v_res_4572_ = l_Lean_Compiler_LCNF_normCode(v_m_4563_, v_pu_boxed_4570_, v_t_boxed_4571_, v_inst_4566_, v_inst_4567_, v_inst_4568_, v_code_4569_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4573_, lean_object* v_e_4574_, lean_object* v_s_4575_, uint8_t v_translator_4576_){
_start:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4578_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4573_, v_s_4575_, v_translator_4576_, v_e_4574_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4580_, lean_object* v_e_4581_, lean_object* v_s_4582_, lean_object* v_translator_4583_, lean_object* v_a_4584_){
_start:
{
uint8_t v_pu_boxed_4585_; uint8_t v_translator_boxed_4586_; lean_object* v_res_4587_; 
v_pu_boxed_4585_ = lean_unbox(v_pu_4580_);
v_translator_boxed_4586_ = lean_unbox(v_translator_4583_);
v_res_4587_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4585_, v_e_4581_, v_s_4582_, v_translator_boxed_4586_);
lean_dec_ref(v_s_4582_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4588_, lean_object* v_e_4589_, lean_object* v_s_4590_, uint8_t v_translator_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4588_, v_e_4589_, v_s_4590_, v_translator_4591_);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4598_, lean_object* v_e_4599_, lean_object* v_s_4600_, lean_object* v_translator_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
uint8_t v_pu_boxed_4607_; uint8_t v_translator_boxed_4608_; lean_object* v_res_4609_; 
v_pu_boxed_4607_ = lean_unbox(v_pu_4598_);
v_translator_boxed_4608_ = lean_unbox(v_translator_4601_);
v_res_4609_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4607_, v_e_4599_, v_s_4600_, v_translator_boxed_4608_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec_ref(v_s_4600_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4610_, lean_object* v_code_4611_, lean_object* v_s_4612_, uint8_t v_translator_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4610_, v_translator_4613_, v_code_4611_, v_s_4612_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4620_, lean_object* v_code_4621_, lean_object* v_s_4622_, lean_object* v_translator_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
uint8_t v_pu_boxed_4629_; uint8_t v_translator_boxed_4630_; lean_object* v_res_4631_; 
v_pu_boxed_4629_ = lean_unbox(v_pu_4620_);
v_translator_boxed_4630_ = lean_unbox(v_translator_4623_);
v_res_4631_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4629_, v_code_4621_, v_s_4622_, v_translator_boxed_4630_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec_ref(v_s_4622_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4638_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4637_, v_a_4635_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4639_);
lean_dec(v_a_4639_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4643_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4654_, lean_object* v_type_4655_, uint8_t v_borrow_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v_a_4664_; lean_object* v___x_4665_; 
v___x_4662_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4663_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4662_, v_a_4658_);
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4664_);
lean_dec_ref(v___x_4663_);
v___x_4665_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4654_, v_a_4664_, v_type_4655_, v_borrow_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4666_, lean_object* v_type_4667_, lean_object* v_borrow_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
uint8_t v_pu_boxed_4674_; uint8_t v_borrow_boxed_4675_; lean_object* v_res_4676_; 
v_pu_boxed_4674_ = lean_unbox(v_pu_4666_);
v_borrow_boxed_4675_ = lean_unbox(v_borrow_4668_);
v_res_4676_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4674_, v_type_4667_, v_borrow_boxed_4675_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4677_){
_start:
{
lean_object* v_config_4679_; lean_object* v___x_4680_; 
v_config_4679_ = lean_ctor_get(v_a_4677_, 0);
lean_inc_ref(v_config_4679_);
v___x_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4680_, 0, v_config_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4681_);
lean_dec_ref(v_a_4681_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4684_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l_Lean_Compiler_LCNF_getConfig(v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4696_, lean_object* v_s_4697_, uint8_t v_phase_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4702_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4699_);
v___x_4703_ = l_Lean_Compiler_LCNF_toConfigOptions(v___x_4702_);
lean_dec_ref(v___x_4702_);
v___x_4704_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
lean_ctor_set_uint8(v___x_4704_, sizeof(void*)*1, v_phase_4698_);
v___x_4705_ = lean_st_mk_ref(v_s_4697_);
lean_inc(v_a_4700_);
lean_inc_ref(v_a_4699_);
lean_inc(v___x_4705_);
v___x_4706_ = lean_apply_5(v_x_4696_, v___x_4704_, v___x_4705_, v_a_4699_, v_a_4700_, lean_box(0));
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4715_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4709_ = v___x_4706_;
v_isShared_4710_ = v_isSharedCheck_4715_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4715_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4711_; lean_object* v___x_4713_; 
v___x_4711_ = lean_st_ref_get(v___x_4705_);
lean_dec(v___x_4705_);
lean_dec(v___x_4711_);
if (v_isShared_4710_ == 0)
{
v___x_4713_ = v___x_4709_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4707_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
else
{
lean_dec(v___x_4705_);
return v___x_4706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4716_, lean_object* v_s_4717_, lean_object* v_phase_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
uint8_t v_phase_boxed_4722_; lean_object* v_res_4723_; 
v_phase_boxed_4722_ = lean_unbox(v_phase_4718_);
v_res_4723_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4716_, v_s_4717_, v_phase_boxed_4722_, v_a_4719_, v_a_4720_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4724_, lean_object* v_x_4725_, lean_object* v_s_4726_, uint8_t v_phase_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4725_, v_s_4726_, v_phase_4727_, v_a_4728_, v_a_4729_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4732_, lean_object* v_x_4733_, lean_object* v_s_4734_, lean_object* v_phase_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
uint8_t v_phase_boxed_4739_; lean_object* v_res_4740_; 
v_phase_boxed_4739_ = lean_unbox(v_phase_4735_);
v_res_4740_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4732_, v_x_4733_, v_s_4734_, v_phase_boxed_4739_, v_a_4736_, v_a_4737_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
return v_res_4740_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg(){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object* v___dummy_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4746_, lean_object* v_00_u03b2_4747_, lean_object* v_inst_4748_, lean_object* v_inst_4749_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4751_, lean_object* v_00_u03b2_4752_, lean_object* v_inst_4753_, lean_object* v_inst_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4751_, v_00_u03b2_4752_, v_inst_4753_, v_inst_4754_);
lean_dec_ref(v_inst_4754_);
lean_dec_ref(v_inst_4753_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg(){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object* v___dummy_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
lean_dec_ref(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4769_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4773_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4774_ = lean_unsigned_to_nat(14u);
v___x_4775_ = lean_unsigned_to_nat(178u);
v___x_4776_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4777_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4778_ = l_mkPanicMessageWithDecl(v___x_4777_, v___x_4776_, v___x_4775_, v___x_4774_, v___x_4773_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4779_, lean_object* v_inst_4780_, lean_object* v_snd_4781_, lean_object* v_inst_4782_, lean_object* v_s_4783_, lean_object* v_e_4784_){
_start:
{
lean_object* v_fst_4785_; lean_object* v_snd_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4801_; 
v_fst_4785_ = lean_ctor_get(v_s_4783_, 0);
v_snd_4786_ = lean_ctor_get(v_s_4783_, 1);
v_isSharedCheck_4801_ = !lean_is_exclusive(v_s_4783_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4788_ = v_s_4783_;
v_isShared_4789_ = v_isSharedCheck_4801_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_snd_4786_);
lean_inc(v_fst_4785_);
lean_dec(v_s_4783_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4801_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___y_4792_; lean_object* v___x_4797_; 
lean_inc_n(v_e_4784_, 2);
v___x_4790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4790_, 0, v_e_4784_);
lean_ctor_set(v___x_4790_, 1, v_fst_4785_);
lean_inc_ref(v_inst_4780_);
lean_inc_ref(v_inst_4779_);
v___x_4797_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4779_, v_inst_4780_, v_snd_4781_, v_e_4784_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4798_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4799_ = l_panic___redArg(v_inst_4782_, v___x_4798_);
v___y_4792_ = v___x_4799_;
goto v___jp_4791_;
}
else
{
lean_object* v_val_4800_; 
v_val_4800_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_val_4800_);
lean_dec_ref_known(v___x_4797_, 1);
v___y_4792_ = v_val_4800_;
goto v___jp_4791_;
}
v___jp_4791_:
{
lean_object* v___x_4793_; lean_object* v___x_4795_; 
v___x_4793_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4779_, v_inst_4780_, v_snd_4786_, v_e_4784_, v___y_4792_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 1, v___x_4793_);
lean_ctor_set(v___x_4788_, 0, v___x_4790_);
v___x_4795_ = v___x_4788_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4796_, 1, v___x_4793_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4802_, lean_object* v_inst_4803_, lean_object* v_snd_4804_, lean_object* v_inst_4805_, lean_object* v_s_4806_, lean_object* v_e_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4802_, v_inst_4803_, v_snd_4804_, v_inst_4805_, v_s_4806_, v_e_4807_);
lean_dec(v_inst_4805_);
lean_dec(v_snd_4804_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4809_, lean_object* v_inst_4810_, lean_object* v_inst_4811_, lean_object* v_oldState_4812_, lean_object* v_newState_4813_, lean_object* v_x_4814_, lean_object* v_s_4815_){
_start:
{
lean_object* v_fst_4816_; lean_object* v_snd_4817_; lean_object* v_fst_4818_; lean_object* v___f_4819_; lean_object* v_newEntries_4820_; lean_object* v___x_4821_; 
v_fst_4816_ = lean_ctor_get(v_newState_4813_, 0);
lean_inc(v_fst_4816_);
v_snd_4817_ = lean_ctor_get(v_newState_4813_, 1);
lean_inc(v_snd_4817_);
lean_dec_ref(v_newState_4813_);
v_fst_4818_ = lean_ctor_get(v_oldState_4812_, 0);
v___f_4819_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4819_, 0, v_inst_4809_);
lean_closure_set(v___f_4819_, 1, v_inst_4810_);
lean_closure_set(v___f_4819_, 2, v_snd_4817_);
lean_closure_set(v___f_4819_, 3, v_inst_4811_);
v_newEntries_4820_ = l_Lean_takeNewEntries___redArg(v_fst_4816_, v_fst_4818_);
v___x_4821_ = l_List_foldl___redArg(v___f_4819_, v_s_4815_, v_newEntries_4820_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4822_, lean_object* v_inst_4823_, lean_object* v_inst_4824_, lean_object* v_oldState_4825_, lean_object* v_newState_4826_, lean_object* v_x_4827_, lean_object* v_s_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4822_, v_inst_4823_, v_inst_4824_, v_oldState_4825_, v_newState_4826_, v_x_4827_, v_s_4828_);
lean_dec(v_x_4827_);
lean_dec_ref(v_oldState_4825_);
return v_res_4829_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4832_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4833_ = lean_box(0);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
lean_ctor_set(v___x_4834_, 1, v___x_4832_);
return v___x_4834_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4835_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4836_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4836_, 0, lean_box(0));
lean_closure_set(v___x_4836_, 1, lean_box(0));
lean_closure_set(v___x_4836_, 2, v___x_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4837_, lean_object* v_inst_4838_, lean_object* v_inst_4839_){
_start:
{
lean_object* v___f_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___f_4841_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4841_, 0, v_inst_4837_);
lean_closure_set(v___f_4841_, 1, v_inst_4838_);
lean_closure_set(v___f_4841_, 2, v_inst_4839_);
v___x_4842_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___f_4841_);
v___x_4844_ = lean_box(0);
v___x_4845_ = l_Lean_registerEnvExtension___redArg(v___x_4842_, v___x_4843_, v___x_4844_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
v_a_4854_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4845_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4845_);
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
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4862_, lean_object* v_inst_4863_, lean_object* v_inst_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4862_, v_inst_4863_, v_inst_4864_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4867_, lean_object* v_00_u03b2_4868_, lean_object* v_inst_4869_, lean_object* v_inst_4870_, lean_object* v_inst_4871_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4869_, v_inst_4870_, v_inst_4871_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4874_, lean_object* v_00_u03b2_4875_, lean_object* v_inst_4876_, lean_object* v_inst_4877_, lean_object* v_inst_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4874_, v_00_u03b2_4875_, v_inst_4876_, v_inst_4877_, v_inst_4878_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4881_, lean_object* v_inst_4882_, lean_object* v_inst_4883_, lean_object* v_b_4884_, lean_object* v_x_4885_){
_start:
{
lean_object* v_fst_4886_; lean_object* v_snd_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4896_; 
v_fst_4886_ = lean_ctor_get(v_x_4885_, 0);
v_snd_4887_ = lean_ctor_get(v_x_4885_, 1);
v_isSharedCheck_4896_ = !lean_is_exclusive(v_x_4885_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4889_ = v_x_4885_;
v_isShared_4890_ = v_isSharedCheck_4896_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_snd_4887_);
lean_inc(v_fst_4886_);
lean_dec(v_x_4885_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4896_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4894_; 
lean_inc(v_a_4881_);
v___x_4891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4891_, 0, v_a_4881_);
lean_ctor_set(v___x_4891_, 1, v_fst_4886_);
v___x_4892_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4882_, v_inst_4883_, v_snd_4887_, v_a_4881_, v_b_4884_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 1, v___x_4892_);
lean_ctor_set(v___x_4889_, 0, v___x_4891_);
v___x_4894_ = v___x_4889_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4891_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4897_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
return v___x_4898_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4899_);
lean_ctor_set(v___x_4900_, 1, v___x_4899_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4901_, lean_object* v_inst_4902_, lean_object* v_ext_4903_, lean_object* v_a_4904_, lean_object* v_b_4905_, lean_object* v_a_4906_){
_start:
{
lean_object* v___f_4908_; lean_object* v___x_4909_; lean_object* v_env_4910_; lean_object* v_nextMacroScope_4911_; lean_object* v_ngen_4912_; lean_object* v_auxDeclNGen_4913_; lean_object* v_traceState_4914_; lean_object* v_recordedDeps_4915_; lean_object* v_messages_4916_; lean_object* v_infoState_4917_; lean_object* v_snapshotTasks_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4932_; 
v___f_4908_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4908_, 0, v_a_4904_);
lean_closure_set(v___f_4908_, 1, v_inst_4901_);
lean_closure_set(v___f_4908_, 2, v_inst_4902_);
lean_closure_set(v___f_4908_, 3, v_b_4905_);
v___x_4909_ = lean_st_ref_take(v_a_4906_);
v_env_4910_ = lean_ctor_get(v___x_4909_, 0);
v_nextMacroScope_4911_ = lean_ctor_get(v___x_4909_, 1);
v_ngen_4912_ = lean_ctor_get(v___x_4909_, 2);
v_auxDeclNGen_4913_ = lean_ctor_get(v___x_4909_, 3);
v_traceState_4914_ = lean_ctor_get(v___x_4909_, 4);
v_recordedDeps_4915_ = lean_ctor_get(v___x_4909_, 6);
v_messages_4916_ = lean_ctor_get(v___x_4909_, 7);
v_infoState_4917_ = lean_ctor_get(v___x_4909_, 8);
v_snapshotTasks_4918_ = lean_ctor_get(v___x_4909_, 9);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4932_ == 0)
{
lean_object* v_unused_4933_; 
v_unused_4933_ = lean_ctor_get(v___x_4909_, 5);
lean_dec(v_unused_4933_);
v___x_4920_ = v___x_4909_;
v_isShared_4921_ = v_isSharedCheck_4932_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_snapshotTasks_4918_);
lean_inc(v_infoState_4917_);
lean_inc(v_messages_4916_);
lean_inc(v_recordedDeps_4915_);
lean_inc(v_traceState_4914_);
lean_inc(v_auxDeclNGen_4913_);
lean_inc(v_ngen_4912_);
lean_inc(v_nextMacroScope_4911_);
lean_inc(v_env_4910_);
lean_dec(v___x_4909_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4932_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_asyncMode_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4928_; 
v_asyncMode_4922_ = lean_ctor_get(v_ext_4903_, 2);
lean_inc(v_asyncMode_4922_);
v___x_4923_ = lean_box(0);
v___x_4924_ = lean_box(0);
v___x_4925_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4903_, v_env_4910_, v___f_4908_, v_asyncMode_4922_, v___x_4924_);
lean_dec(v_asyncMode_4922_);
v___x_4926_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 5, v___x_4926_);
lean_ctor_set(v___x_4920_, 0, v___x_4925_);
v___x_4928_ = v___x_4920_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4925_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_nextMacroScope_4911_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_ngen_4912_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_auxDeclNGen_4913_);
lean_ctor_set(v_reuseFailAlloc_4931_, 4, v_traceState_4914_);
lean_ctor_set(v_reuseFailAlloc_4931_, 5, v___x_4926_);
lean_ctor_set(v_reuseFailAlloc_4931_, 6, v_recordedDeps_4915_);
lean_ctor_set(v_reuseFailAlloc_4931_, 7, v_messages_4916_);
lean_ctor_set(v_reuseFailAlloc_4931_, 8, v_infoState_4917_);
lean_ctor_set(v_reuseFailAlloc_4931_, 9, v_snapshotTasks_4918_);
v___x_4928_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = lean_st_ref_put(v_a_4906_, v___x_4928_);
v___x_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4923_);
return v___x_4930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4934_, lean_object* v_inst_4935_, lean_object* v_ext_4936_, lean_object* v_a_4937_, lean_object* v_b_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4934_, v_inst_4935_, v_ext_4936_, v_a_4937_, v_b_4938_, v_a_4939_);
lean_dec(v_a_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4942_, lean_object* v_00_u03b2_4943_, lean_object* v_inst_4944_, lean_object* v_inst_4945_, lean_object* v_inst_4946_, lean_object* v_ext_4947_, lean_object* v_a_4948_, lean_object* v_b_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4944_, v_inst_4945_, v_ext_4947_, v_a_4948_, v_b_4949_, v_a_4951_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4954_, lean_object* v_00_u03b2_4955_, lean_object* v_inst_4956_, lean_object* v_inst_4957_, lean_object* v_inst_4958_, lean_object* v_ext_4959_, lean_object* v_a_4960_, lean_object* v_b_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4954_, v_00_u03b2_4955_, v_inst_4956_, v_inst_4957_, v_inst_4958_, v_ext_4959_, v_a_4960_, v_b_4961_, v_a_4962_, v_a_4963_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_inst_4958_);
return v_res_4965_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_4966_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4967_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0);
v___x_4968_ = lean_box(0);
v___x_4969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
lean_ctor_set(v___x_4969_, 1, v___x_4967_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4970_, lean_object* v_inst_4971_, lean_object* v_ext_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v_env_4978_; lean_object* v_asyncMode_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v_snd_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4976_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1);
v___x_4977_ = lean_st_ref_get(v_a_4974_);
v_env_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc_ref(v_env_4978_);
lean_dec(v___x_4977_);
v_asyncMode_4979_ = lean_ctor_get(v_ext_4972_, 2);
v___x_4980_ = lean_box(0);
v___x_4981_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4976_, v_ext_4972_, v_env_4978_, v_asyncMode_4979_, v___x_4980_);
v_snd_4982_ = lean_ctor_get(v___x_4981_, 1);
lean_inc(v_snd_4982_);
lean_dec(v___x_4981_);
v___x_4983_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4970_, v_inst_4971_, v_snd_4982_, v_a_4973_);
lean_dec(v_snd_4982_);
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4985_, lean_object* v_inst_4986_, lean_object* v_ext_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4985_, v_inst_4986_, v_ext_4987_, v_a_4988_, v_a_4989_);
lean_dec(v_a_4989_);
lean_dec_ref(v_ext_4987_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4992_, lean_object* v_00_u03b2_4993_, lean_object* v_inst_4994_, lean_object* v_inst_4995_, lean_object* v_inst_4996_, lean_object* v_ext_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4994_, v_inst_4995_, v_ext_4997_, v_a_4998_, v_a_5000_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5003_, lean_object* v_00_u03b2_5004_, lean_object* v_inst_5005_, lean_object* v_inst_5006_, lean_object* v_inst_5007_, lean_object* v_ext_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5003_, v_00_u03b2_5004_, v_inst_5005_, v_inst_5006_, v_inst_5007_, v_ext_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec_ref(v_ext_5008_);
lean_dec(v_inst_5007_);
return v_res_5013_;
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
