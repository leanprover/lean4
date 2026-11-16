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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toConfigOptions(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_takeNewEntries___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "CacheExtension"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "register"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(114, 63, 216, 176, 94, 170, 18, 246)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_3),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(147, 186, 41, 27, 108, 56, 19, 46)}};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_22_){
_start:
{
lean_inc(v_base_22_);
return v_base_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_23_);
lean_dec(v_base_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_base_28_){
_start:
{
lean_inc(v_base_28_);
return v_base_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_base_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_base_32_);
lean_dec(v_base_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_35_){
_start:
{
lean_inc(v_mono_35_);
return v_mono_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_36_);
lean_dec(v_mono_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_mono_41_){
_start:
{
lean_inc(v_mono_41_);
return v_mono_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_mono_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_mono_45_);
lean_dec(v_mono_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_48_){
_start:
{
lean_inc(v_impure_48_);
return v_impure_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_49_);
lean_dec(v_impure_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_impure_54_){
_start:
{
lean_inc(v_impure_54_);
return v_impure_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_impure_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_impure_58_);
lean_dec(v_impure_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_nat_dec_le(v_n_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_dec_le(v_n_63_, v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 2;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object* v_n_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_71_);
lean_dec(v_n_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_74_, uint8_t v_y_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_76_ = lean_box(v_x_74_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_box(v_y_75_);
v___x_79_ = lean_obj_tag_nat(v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v_x_23__boxed_83_; uint8_t v_y_24__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_x_23__boxed_83_ = lean_unbox(v_x_81_);
v_y_24__boxed_84_ = lean_unbox(v_y_82_);
v_res_85_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_23__boxed_83_, v_y_24__boxed_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_87_){
_start:
{
if (v_x_87_ == 2)
{
uint8_t v___x_88_; 
v___x_88_ = 1;
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_90_){
_start:
{
uint8_t v_x_23__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_23__boxed_91_ = lean_unbox(v_x_90_);
v_res_92_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_unsigned_to_nat(16u);
v___x_96_ = lean_mk_array(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v___x_100_);
lean_ctor_set(v___x_101_, 4, v___x_100_);
lean_ctor_set(v___x_101_, 5, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_108_ = 0;
v___x_109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___y_113_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_137_ = lean_apply_5(v___y_130_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_139_ = lean_apply_6(v___y_131_, v_a_138_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
return v___x_139_;
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v___y_131_);
v_a_140_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_137_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_137_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_148_, v_00_u03b2_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_instMonadEIO___redArg();
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_160_ = l_StateRefT_x27_instMonad___redArg(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_165_; lean_object* v_toApplicative_166_; lean_object* v_toFunctor_167_; lean_object* v_toSeq_168_; lean_object* v_toSeqLeft_169_; lean_object* v_toSeqRight_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_toApplicative_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_209_; 
v___x_165_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_166_ = lean_ctor_get(v___x_165_, 0);
v_toFunctor_167_ = lean_ctor_get(v_toApplicative_166_, 0);
v_toSeq_168_ = lean_ctor_get(v_toApplicative_166_, 2);
v_toSeqLeft_169_ = lean_ctor_get(v_toApplicative_166_, 3);
v_toSeqRight_170_ = lean_ctor_get(v_toApplicative_166_, 4);
v___f_171_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_172_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_167_, 2);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_173_, 0, v_toFunctor_167_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_174_, 0, v_toFunctor_167_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___f_173_);
lean_ctor_set(v___x_175_, 1, v___f_174_);
lean_inc(v_toSeqRight_170_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_176_, 0, v_toSeqRight_170_);
lean_inc(v_toSeqLeft_169_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeqLeft_169_);
lean_inc(v_toSeq_168_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeq_168_);
v___x_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_179_, 0, v___x_175_);
lean_ctor_set(v___x_179_, 1, v___f_171_);
lean_ctor_set(v___x_179_, 2, v___f_178_);
lean_ctor_set(v___x_179_, 3, v___f_177_);
lean_ctor_set(v___x_179_, 4, v___f_176_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___f_172_);
v___x_181_ = l_StateRefT_x27_instMonad___redArg(v___x_180_);
v_toApplicative_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_181_, 1);
lean_dec(v_unused_210_);
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_209_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_toApplicative_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_209_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_toFunctor_186_; lean_object* v_toSeq_187_; lean_object* v_toSeqLeft_188_; lean_object* v_toSeqRight_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_207_; 
v_toFunctor_186_ = lean_ctor_get(v_toApplicative_182_, 0);
v_toSeq_187_ = lean_ctor_get(v_toApplicative_182_, 2);
v_toSeqLeft_188_ = lean_ctor_get(v_toApplicative_182_, 3);
v_toSeqRight_189_ = lean_ctor_get(v_toApplicative_182_, 4);
v_isSharedCheck_207_ = !lean_is_exclusive(v_toApplicative_182_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_toApplicative_182_, 1);
lean_dec(v_unused_208_);
v___x_191_ = v_toApplicative_182_;
v_isShared_192_ = v_isSharedCheck_207_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_toSeqRight_189_);
lean_inc(v_toSeqLeft_188_);
lean_inc(v_toSeq_187_);
lean_inc(v_toFunctor_186_);
lean_dec(v_toApplicative_182_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_207_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___x_202_; 
v___f_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_194_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_186_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_195_, 0, v_toFunctor_186_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_196_, 0, v_toFunctor_186_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___f_195_);
lean_ctor_set(v___x_197_, 1, v___f_196_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeqRight_189_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeqLeft_188_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_200_, 0, v_toSeq_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v___f_198_);
lean_ctor_set(v___x_191_, 3, v___f_199_);
lean_ctor_set(v___x_191_, 2, v___f_200_);
lean_ctor_set(v___x_191_, 1, v___f_193_);
lean_ctor_set(v___x_191_, 0, v___x_197_);
v___x_202_ = v___x_191_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___f_193_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v___f_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v___f_198_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___f_194_);
lean_ctor_set(v___x_184_, 0, v___x_202_);
v___x_204_ = v___x_184_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___f_194_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_211_, lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_config_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_config_218_ = lean_ctor_get(v_a_213_, 0);
lean_inc_ref(v_config_218_);
v___x_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_219_, 0, v_config_218_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v_phase_211_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
v___x_220_ = lean_apply_5(v_x_212_, v___x_219_, v_a_214_, v_a_215_, v_a_216_, lean_box(0));
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
uint8_t v_phase_boxed_228_; lean_object* v_res_229_; 
v_phase_boxed_228_ = lean_unbox(v_phase_221_);
v_res_229_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_228_, v_x_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_230_, uint8_t v_phase_231_, lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_config_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_config_238_ = lean_ctor_get(v_a_233_, 0);
lean_inc_ref(v_config_238_);
v___x_239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_239_, 0, v_config_238_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v_phase_231_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc(v_a_234_);
v___x_240_ = lean_apply_5(v_x_232_, v___x_239_, v_a_234_, v_a_235_, v_a_236_, lean_box(0));
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_241_, lean_object* v_phase_242_, lean_object* v_x_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_phase_boxed_249_; lean_object* v_res_250_; 
v_phase_boxed_249_ = lean_unbox(v_phase_242_);
v_res_250_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_241_, v_phase_boxed_249_, v_x_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_251_){
_start:
{
uint8_t v_phase_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_phase_253_ = lean_ctor_get_uint8(v_a_251_, sizeof(void*)*1);
v___x_254_ = lean_box(v_phase_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_256_);
lean_dec_ref(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Compiler_LCNF_getPhase(v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_284_; 
v___x_273_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_271_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_284_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint8_t v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_278_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
v___x_279_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_278_);
v___x_280_ = lean_box(v___x_279_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_280_);
v___x_282_ = v___x_276_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_285_);
lean_dec_ref(v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_288_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Compiler_LCNF_getPurity(v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_318_; 
v___x_302_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_300_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_318_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
uint8_t v___x_307_; 
v___x_307_ = lean_unbox(v_a_303_);
lean_dec(v_a_303_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = 1;
v___x_309_ = lean_box(v___x_308_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = 0;
v___x_314_ = lean_box(v___x_313_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_314_);
v___x_316_ = v___x_305_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_319_);
lean_dec_ref(v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_322_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
lean_ctor_set(v___x_339_, 3, v___x_338_);
lean_ctor_set(v___x_339_, 4, v___x_337_);
lean_ctor_set(v___x_339_, 5, v___x_337_);
lean_ctor_set(v___x_339_, 6, v___x_337_);
lean_ctor_set(v___x_339_, 7, v___x_337_);
lean_ctor_set(v___x_339_, 8, v___x_337_);
lean_ctor_set(v___x_339_, 9, v___x_337_);
lean_ctor_set(v___x_339_, 10, v___x_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = lean_st_ref_get(v___y_342_);
v___x_349_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_341_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_371_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_371_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_371_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_371_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_lctx_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_369_; 
v_lctx_354_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_348_, 1);
lean_dec(v_unused_370_);
v___x_356_ = v___x_348_;
v_isShared_357_ = v_isSharedCheck_369_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_lctx_354_);
lean_dec(v___x_348_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_369_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_358_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
v___x_359_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_354_, v___x_358_);
lean_dec_ref(v_lctx_354_);
v___x_360_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_343_);
v___x_361_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_362_, 0, v_env_347_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
lean_ctor_set(v___x_362_, 2, v___x_359_);
lean_ctor_set(v___x_362_, 3, v___x_360_);
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 3);
lean_ctor_set(v___x_356_, 1, v_msgData_340_);
lean_ctor_set(v___x_356_, 0, v___x_362_);
v___x_364_ = v___x_356_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_msgData_340_);
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
lean_dec(v___x_348_);
lean_dec_ref(v_env_347_);
lean_dec_ref(v_msgData_340_);
v_a_372_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_349_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_349_);
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
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v_env_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_ref_395_ = lean_ctor_get(v___y_392_, 2);
v___x_396_ = lean_st_ref_get(v___y_393_);
v_env_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_env_397_);
lean_dec(v___x_396_);
v___x_398_ = lean_st_ref_get(v___y_391_);
v___x_399_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_390_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_422_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_422_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_422_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_422_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_lctx_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_420_; 
v_lctx_404_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_398_, 1);
lean_dec(v_unused_421_);
v___x_406_ = v___x_398_;
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_lctx_404_);
lean_dec(v___x_398_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_408_ = lean_unbox(v_a_400_);
lean_dec(v_a_400_);
v___x_409_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_404_, v___x_408_);
lean_dec_ref(v_lctx_404_);
v___x_410_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_392_);
v___x_411_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_412_, 0, v_env_397_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
lean_ctor_set(v___x_412_, 3, v___x_410_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 3);
lean_ctor_set(v___x_406_, 1, v_msg_389_);
lean_ctor_set(v___x_406_, 0, v___x_412_);
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_msg_389_);
v___x_414_ = v_reuseFailAlloc_419_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_inc(v_ref_395_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_ref_395_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 1);
lean_ctor_set(v___x_402_, 0, v___x_415_);
v___x_417_ = v___x_402_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v___x_398_);
lean_dec_ref(v_env_397_);
lean_dec_ref(v_msg_389_);
v_a_423_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_399_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_399_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_446_, lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_446_, v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v_key_457_; lean_object* v_value_458_; lean_object* v_tail_459_; uint8_t v___x_460_; 
v_key_457_ = lean_ctor_get(v_x_455_, 0);
v_value_458_ = lean_ctor_get(v_x_455_, 1);
v_tail_459_ = lean_ctor_get(v_x_455_, 2);
v___x_460_ = l_Lean_instBEqFVarId_beq(v_key_457_, v_a_454_);
if (v___x_460_ == 0)
{
v_x_455_ = v_tail_459_;
goto _start;
}
else
{
lean_object* v___x_462_; 
lean_inc(v_value_458_);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_value_458_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_buckets_468_; lean_object* v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_buckets_468_ = lean_ctor_get(v_m_466_, 1);
v___x_469_ = lean_array_get_size(v_buckets_468_);
v___x_470_ = l_Lean_instHashableFVarId_hash(v_a_467_);
v___x_471_ = 32ULL;
v___x_472_ = lean_uint64_shift_right(v___x_470_, v___x_471_);
v_fold_473_ = lean_uint64_xor(v___x_470_, v___x_472_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_469_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v___x_482_ = lean_array_uget_borrowed(v_buckets_468_, v___x_481_);
v___x_483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_467_, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_484_, v_a_485_);
lean_dec(v_a_485_);
lean_dec_ref(v_m_484_);
return v_res_486_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_lctx_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_562_; 
v___x_496_ = lean_st_ref_get(v_a_492_);
v_lctx_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_496_, 1);
lean_dec(v_unused_563_);
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_562_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_lctx_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_562_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_491_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_553_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_553_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_553_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_553_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___y_507_; lean_object* v___y_521_; lean_object* v___y_536_; uint8_t v___x_550_; 
v___x_550_ = lean_unbox(v_a_502_);
if (v___x_550_ == 0)
{
lean_object* v_letDeclsPure_551_; 
v_letDeclsPure_551_ = lean_ctor_get(v_lctx_497_, 2);
lean_inc_ref(v_letDeclsPure_551_);
v___y_536_ = v_letDeclsPure_551_;
goto v___jp_535_;
}
else
{
lean_object* v_letDeclsImpure_552_; 
v_letDeclsImpure_552_ = lean_ctor_get(v_lctx_497_, 3);
lean_inc_ref(v_letDeclsImpure_552_);
v___y_536_ = v_letDeclsImpure_552_;
goto v___jp_535_;
}
v___jp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_507_, v_fvarId_490_);
lean_dec_ref(v___y_507_);
if (lean_obj_tag(v___x_508_) == 1)
{
lean_object* v_val_509_; lean_object* v_type_510_; lean_object* v___x_512_; 
lean_del_object(v___x_499_);
lean_dec(v_fvarId_490_);
v_val_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___x_508_, 1);
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
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec(v___x_508_);
lean_del_object(v___x_504_);
v___x_514_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_515_ = l_Lean_MessageData_ofName(v_fvarId_490_);
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 7);
lean_ctor_set(v___x_499_, 1, v___x_515_);
lean_ctor_set(v___x_499_, 0, v___x_514_);
v___x_517_ = v___x_499_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_519_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_517_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
return v___x_518_;
}
}
}
v___jp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_521_, v_fvarId_490_);
lean_dec_ref(v___y_521_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_del_object(v___x_499_);
lean_dec_ref(v_lctx_497_);
lean_dec(v_fvarId_490_);
v_val_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_531_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_type_527_; lean_object* v___x_529_; 
v_type_527_ = lean_ctor_get(v_val_523_, 2);
lean_inc_ref(v_type_527_);
lean_dec(v_val_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
lean_ctor_set(v___x_525_, 0, v_type_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_type_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
uint8_t v___x_532_; 
lean_dec(v___x_522_);
v___x_532_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_532_ == 0)
{
lean_object* v_funDeclsPure_533_; 
v_funDeclsPure_533_ = lean_ctor_get(v_lctx_497_, 4);
lean_inc_ref(v_funDeclsPure_533_);
lean_dec_ref(v_lctx_497_);
v___y_507_ = v_funDeclsPure_533_;
goto v___jp_506_;
}
else
{
lean_object* v_funDeclsImpure_534_; 
v_funDeclsImpure_534_ = lean_ctor_get(v_lctx_497_, 5);
lean_inc_ref(v_funDeclsImpure_534_);
lean_dec_ref(v_lctx_497_);
v___y_507_ = v_funDeclsImpure_534_;
goto v___jp_506_;
}
}
}
v___jp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_536_, v_fvarId_490_);
lean_dec_ref(v___y_536_);
if (lean_obj_tag(v___x_537_) == 1)
{
lean_object* v_val_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_del_object(v___x_499_);
lean_dec_ref(v_lctx_497_);
lean_dec(v_fvarId_490_);
v_val_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_val_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_type_542_; lean_object* v___x_544_; 
v_type_542_ = lean_ctor_get(v_val_538_, 2);
lean_inc_ref(v_type_542_);
lean_dec(v_val_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 0);
lean_ctor_set(v___x_540_, 0, v_type_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_type_542_);
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
uint8_t v___x_547_; 
lean_dec(v___x_537_);
v___x_547_ = lean_unbox(v_a_502_);
if (v___x_547_ == 0)
{
lean_object* v_paramsPure_548_; 
v_paramsPure_548_ = lean_ctor_get(v_lctx_497_, 0);
lean_inc_ref(v_paramsPure_548_);
v___y_521_ = v_paramsPure_548_;
goto v___jp_520_;
}
else
{
lean_object* v_paramsImpure_549_; 
v_paramsImpure_549_ = lean_ctor_get(v_lctx_497_, 1);
lean_inc_ref(v_paramsImpure_549_);
v___y_521_ = v_paramsImpure_549_;
goto v___jp_520_;
}
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_499_);
lean_dec_ref(v_lctx_497_);
lean_dec(v_fvarId_490_);
v_a_554_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_501_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_501_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Compiler_LCNF_getType(v_fvarId_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_571_, lean_object* v_m_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_572_, v_a_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_575_, lean_object* v_m_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_575_, v_m_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_m_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_579_, lean_object* v_a_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_583_, lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_583_, v_a_584_, v_x_585_);
lean_dec(v_x_585_);
lean_dec(v_a_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; lean_object* v_lctx_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_659_; 
v___x_593_ = lean_st_ref_get(v_a_589_);
v_lctx_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_593_, 1);
lean_dec(v_unused_660_);
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_659_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_lctx_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_659_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_588_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_650_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_650_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_650_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_650_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; lean_object* v___y_618_; lean_object* v___y_633_; uint8_t v___x_647_; 
v___x_647_ = lean_unbox(v_a_599_);
if (v___x_647_ == 0)
{
lean_object* v_letDeclsPure_648_; 
v_letDeclsPure_648_ = lean_ctor_get(v_lctx_594_, 2);
lean_inc_ref(v_letDeclsPure_648_);
v___y_633_ = v_letDeclsPure_648_;
goto v___jp_632_;
}
else
{
lean_object* v_letDeclsImpure_649_; 
v_letDeclsImpure_649_ = lean_ctor_get(v_lctx_594_, 3);
lean_inc_ref(v_letDeclsImpure_649_);
v___y_633_ = v_letDeclsImpure_649_;
goto v___jp_632_;
}
v___jp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_604_, v_fvarId_587_);
lean_dec_ref(v___y_604_);
if (lean_obj_tag(v___x_605_) == 1)
{
lean_object* v_val_606_; lean_object* v_binderName_607_; lean_object* v___x_609_; 
lean_del_object(v___x_596_);
lean_dec(v_fvarId_587_);
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_605_, 1);
v_binderName_607_ = lean_ctor_get(v_val_606_, 1);
lean_inc(v_binderName_607_);
lean_dec(v_val_606_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_binderName_607_);
v___x_609_ = v___x_601_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_binderName_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
lean_dec(v___x_605_);
lean_del_object(v___x_601_);
v___x_611_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_612_ = l_Lean_MessageData_ofName(v_fvarId_587_);
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 7);
lean_ctor_set(v___x_596_, 1, v___x_612_);
lean_ctor_set(v___x_596_, 0, v___x_611_);
v___x_614_ = v___x_596_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_614_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
return v___x_615_;
}
}
}
v___jp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_618_, v_fvarId_587_);
lean_dec_ref(v___y_618_);
if (lean_obj_tag(v___x_619_) == 1)
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
lean_del_object(v___x_601_);
lean_dec(v_a_599_);
lean_del_object(v___x_596_);
lean_dec_ref(v_lctx_594_);
lean_dec(v_fvarId_587_);
v_val_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_628_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_binderName_624_; lean_object* v___x_626_; 
v_binderName_624_ = lean_ctor_get(v_val_620_, 1);
lean_inc(v_binderName_624_);
lean_dec(v_val_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 0);
lean_ctor_set(v___x_622_, 0, v_binderName_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_binderName_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
uint8_t v___x_629_; 
lean_dec(v___x_619_);
v___x_629_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_629_ == 0)
{
lean_object* v_funDeclsPure_630_; 
v_funDeclsPure_630_ = lean_ctor_get(v_lctx_594_, 4);
lean_inc_ref(v_funDeclsPure_630_);
lean_dec_ref(v_lctx_594_);
v___y_604_ = v_funDeclsPure_630_;
goto v___jp_603_;
}
else
{
lean_object* v_funDeclsImpure_631_; 
v_funDeclsImpure_631_ = lean_ctor_get(v_lctx_594_, 5);
lean_inc_ref(v_funDeclsImpure_631_);
lean_dec_ref(v_lctx_594_);
v___y_604_ = v_funDeclsImpure_631_;
goto v___jp_603_;
}
}
}
v___jp_632_:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_633_, v_fvarId_587_);
lean_dec_ref(v___y_633_);
if (lean_obj_tag(v___x_634_) == 1)
{
lean_object* v_val_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
lean_del_object(v___x_601_);
lean_dec(v_a_599_);
lean_del_object(v___x_596_);
lean_dec_ref(v_lctx_594_);
lean_dec(v_fvarId_587_);
v_val_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_val_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_binderName_639_; lean_object* v___x_641_; 
v_binderName_639_ = lean_ctor_get(v_val_635_, 1);
lean_inc(v_binderName_639_);
lean_dec(v_val_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
lean_ctor_set(v___x_637_, 0, v_binderName_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_binderName_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
uint8_t v___x_644_; 
lean_dec(v___x_634_);
v___x_644_ = lean_unbox(v_a_599_);
if (v___x_644_ == 0)
{
lean_object* v_paramsPure_645_; 
v_paramsPure_645_ = lean_ctor_get(v_lctx_594_, 0);
lean_inc_ref(v_paramsPure_645_);
v___y_618_ = v_paramsPure_645_;
goto v___jp_617_;
}
else
{
lean_object* v_paramsImpure_646_; 
v_paramsImpure_646_ = lean_ctor_get(v_lctx_594_, 1);
lean_inc_ref(v_paramsImpure_646_);
v___y_618_ = v_paramsImpure_646_;
goto v___jp_617_;
}
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_del_object(v___x_596_);
lean_dec_ref(v_lctx_594_);
lean_dec(v_fvarId_587_);
v_a_651_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_598_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_598_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_668_, lean_object* v_fvarId_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_672_; lean_object* v___y_674_; 
v___x_672_ = lean_st_ref_get(v_a_670_);
if (v_pu_668_ == 0)
{
lean_object* v_lctx_677_; lean_object* v_paramsPure_678_; 
v_lctx_677_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_lctx_677_);
lean_dec(v___x_672_);
v_paramsPure_678_ = lean_ctor_get(v_lctx_677_, 0);
lean_inc_ref(v_paramsPure_678_);
lean_dec_ref(v_lctx_677_);
v___y_674_ = v_paramsPure_678_;
goto v___jp_673_;
}
else
{
lean_object* v_lctx_679_; lean_object* v_paramsImpure_680_; 
v_lctx_679_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_lctx_679_);
lean_dec(v___x_672_);
v_paramsImpure_680_ = lean_ctor_get(v_lctx_679_, 1);
lean_inc_ref(v_paramsImpure_680_);
lean_dec_ref(v_lctx_679_);
v___y_674_ = v_paramsImpure_680_;
goto v___jp_673_;
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_674_, v_fvarId_669_);
lean_dec_ref(v___y_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_681_, lean_object* v_fvarId_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
uint8_t v_pu_boxed_685_; lean_object* v_res_686_; 
v_pu_boxed_685_ = lean_unbox(v_pu_681_);
v_res_686_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_685_, v_fvarId_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec(v_fvarId_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_687_, lean_object* v_fvarId_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_687_, v_fvarId_688_, v_a_690_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_695_, lean_object* v_fvarId_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_pu_boxed_702_; lean_object* v_res_703_; 
v_pu_boxed_702_ = lean_unbox(v_pu_695_);
v_res_703_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_702_, v_fvarId_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_fvarId_696_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_704_, lean_object* v_fvarId_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___y_710_; 
v___x_708_ = lean_st_ref_get(v_a_706_);
if (v_pu_704_ == 0)
{
lean_object* v_lctx_713_; lean_object* v_letDeclsPure_714_; 
v_lctx_713_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_lctx_713_);
lean_dec(v___x_708_);
v_letDeclsPure_714_ = lean_ctor_get(v_lctx_713_, 2);
lean_inc_ref(v_letDeclsPure_714_);
lean_dec_ref(v_lctx_713_);
v___y_710_ = v_letDeclsPure_714_;
goto v___jp_709_;
}
else
{
lean_object* v_lctx_715_; lean_object* v_letDeclsImpure_716_; 
v_lctx_715_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_lctx_715_);
lean_dec(v___x_708_);
v_letDeclsImpure_716_ = lean_ctor_get(v_lctx_715_, 3);
lean_inc_ref(v_letDeclsImpure_716_);
lean_dec_ref(v_lctx_715_);
v___y_710_ = v_letDeclsImpure_716_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_710_, v_fvarId_705_);
lean_dec_ref(v___y_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_717_, lean_object* v_fvarId_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
uint8_t v_pu_boxed_721_; lean_object* v_res_722_; 
v_pu_boxed_721_ = lean_unbox(v_pu_717_);
v_res_722_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_721_, v_fvarId_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec(v_fvarId_718_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_723_, lean_object* v_fvarId_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_723_, v_fvarId_724_, v_a_726_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_731_, lean_object* v_fvarId_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
uint8_t v_pu_boxed_738_; lean_object* v_res_739_; 
v_pu_boxed_738_ = lean_unbox(v_pu_731_);
v_res_739_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_738_, v_fvarId_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_fvarId_732_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_740_, lean_object* v_fvarId_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___y_746_; 
v___x_744_ = lean_st_ref_get(v_a_742_);
if (v_pu_740_ == 0)
{
lean_object* v_lctx_749_; lean_object* v_funDeclsPure_750_; 
v_lctx_749_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_lctx_749_);
lean_dec(v___x_744_);
v_funDeclsPure_750_ = lean_ctor_get(v_lctx_749_, 4);
lean_inc_ref(v_funDeclsPure_750_);
lean_dec_ref(v_lctx_749_);
v___y_746_ = v_funDeclsPure_750_;
goto v___jp_745_;
}
else
{
lean_object* v_lctx_751_; lean_object* v_funDeclsImpure_752_; 
v_lctx_751_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_lctx_751_);
lean_dec(v___x_744_);
v_funDeclsImpure_752_ = lean_ctor_get(v_lctx_751_, 5);
lean_inc_ref(v_funDeclsImpure_752_);
lean_dec_ref(v_lctx_751_);
v___y_746_ = v_funDeclsImpure_752_;
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_746_, v_fvarId_741_);
lean_dec_ref(v___y_746_);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_753_, lean_object* v_fvarId_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_pu_boxed_757_; lean_object* v_res_758_; 
v_pu_boxed_757_ = lean_unbox(v_pu_753_);
v_res_758_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_757_, v_fvarId_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec(v_fvarId_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_759_, lean_object* v_fvarId_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_759_, v_fvarId_760_, v_a_762_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_767_, lean_object* v_fvarId_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v_pu_boxed_774_; lean_object* v_res_775_; 
v_pu_boxed_774_ = lean_unbox(v_pu_767_);
v_res_775_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_774_, v_fvarId_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_fvarId_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_776_, lean_object* v_fvarId_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_801_; 
v___x_780_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_776_, v_fvarId_777_, v_a_778_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_801_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_801_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_801_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
if (lean_obj_tag(v_a_781_) == 1)
{
lean_object* v_val_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_796_; 
v_val_785_ = lean_ctor_get(v_a_781_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_781_);
if (v_isSharedCheck_796_ == 0)
{
v___x_787_ = v_a_781_;
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_val_785_);
lean_dec(v_a_781_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_value_789_; lean_object* v___x_791_; 
v_value_789_ = lean_ctor_get(v_val_785_, 3);
lean_inc(v_value_789_);
lean_dec(v_val_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_value_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_value_789_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_791_);
v___x_793_ = v___x_783_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec(v_a_781_);
v___x_797_ = lean_box(0);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_797_);
v___x_799_ = v___x_783_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_802_, lean_object* v_fvarId_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_pu_boxed_806_; lean_object* v_res_807_; 
v_pu_boxed_806_ = lean_unbox(v_pu_802_);
v_res_807_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_806_, v_fvarId_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec(v_fvarId_803_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_808_, lean_object* v_fvarId_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_808_, v_fvarId_809_, v_a_811_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_816_, lean_object* v_fvarId_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
uint8_t v_pu_boxed_823_; lean_object* v_res_824_; 
v_pu_boxed_823_ = lean_unbox(v_pu_816_);
v_res_824_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_823_, v_fvarId_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_fvarId_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
uint8_t v___x_833_; lean_object* v___x_834_; 
v___x_833_ = 0;
v___x_834_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_833_, v_fvarId_825_, v_a_826_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_862_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_862_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_862_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_862_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
if (lean_obj_tag(v_a_835_) == 1)
{
lean_object* v_val_839_; 
v_val_839_ = lean_ctor_get(v_a_835_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v_a_835_, 1);
if (lean_obj_tag(v_val_839_) == 3)
{
lean_object* v_declName_840_; lean_object* v___x_841_; lean_object* v_env_848_; uint8_t v___x_849_; lean_object* v___x_850_; 
v_declName_840_ = lean_ctor_get(v_val_839_, 0);
lean_inc(v_declName_840_);
lean_dec_ref_known(v_val_839_, 3);
v___x_841_ = lean_st_ref_get(v_a_827_);
v_env_848_ = lean_ctor_get(v___x_841_, 0);
lean_inc_ref(v_env_848_);
lean_dec(v___x_841_);
v___x_849_ = 0;
v___x_850_ = l_Lean_Environment_find_x3f(v_env_848_, v_declName_840_, v___x_849_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_object* v_val_851_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
if (lean_obj_tag(v_val_851_) == 6)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_860_; 
lean_del_object(v___x_837_);
v_isSharedCheck_860_ = !lean_is_exclusive(v_val_851_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_val_851_, 0);
lean_dec(v_unused_861_);
v___x_853_ = v_val_851_;
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_val_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = 1;
v___x_856_ = lean_box(v___x_855_);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 0);
lean_ctor_set(v___x_853_, 0, v___x_856_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_dec(v_val_851_);
goto v___jp_842_;
}
}
else
{
lean_dec(v___x_850_);
goto v___jp_842_;
}
v___jp_842_:
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = 0;
v___x_844_ = lean_box(v___x_843_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_844_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_dec(v_val_839_);
lean_del_object(v___x_837_);
goto v___jp_829_;
}
}
else
{
lean_del_object(v___x_837_);
lean_dec(v_a_835_);
goto v___jp_829_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_834_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_834_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
v___jp_829_:
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = 0;
v___x_831_ = lean_box(v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
lean_dec(v_fvarId_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_876_, v_a_878_, v_a_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_fvarId_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
if (lean_obj_tag(v_arg_890_) == 1)
{
lean_object* v_fvarId_894_; lean_object* v___x_895_; 
v_fvarId_894_ = lean_ctor_get(v_arg_890_, 0);
v___x_895_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_894_, v_a_891_, v_a_892_);
return v___x_895_;
}
else
{
uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = 0;
v___x_897_ = lean_box(v___x_896_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_arg_899_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_904_, lean_object* v_arg_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_905_, v_a_907_, v_a_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_912_, lean_object* v_arg_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
uint8_t v_pu_boxed_919_; lean_object* v_res_920_; 
v_pu_boxed_919_ = lean_unbox(v_pu_912_);
v_res_920_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_919_, v_arg_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_arg_913_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_924_, lean_object* v_fvarId_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_944_; 
v___x_931_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_924_, v_fvarId_925_, v_a_927_);
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_944_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
if (lean_obj_tag(v_a_932_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_938_; 
lean_dec(v_fvarId_925_);
v_val_936_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v_a_932_, 1);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_val_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_val_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_del_object(v___x_934_);
lean_dec(v_a_932_);
v___x_940_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_941_ = l_Lean_MessageData_ofName(v_fvarId_925_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_942_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_945_, lean_object* v_fvarId_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
uint8_t v_pu_boxed_952_; lean_object* v_res_953_; 
v_pu_boxed_952_ = lean_unbox(v_pu_945_);
v_res_953_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_952_, v_fvarId_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_953_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_957_, lean_object* v_fvarId_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_977_; 
v___x_964_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_957_, v_fvarId_958_, v_a_960_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_977_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
if (lean_obj_tag(v_a_965_) == 1)
{
lean_object* v_val_969_; lean_object* v___x_971_; 
lean_dec(v_fvarId_958_);
v_val_969_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v_a_965_, 1);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_val_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_val_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_del_object(v___x_967_);
lean_dec(v_a_965_);
v___x_973_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_974_ = l_Lean_MessageData_ofName(v_fvarId_958_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_975_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_978_, lean_object* v_fvarId_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
uint8_t v_pu_boxed_985_; lean_object* v_res_986_; 
v_pu_boxed_985_ = lean_unbox(v_pu_978_);
v_res_986_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_985_, v_fvarId_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_990_, lean_object* v_fvarId_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1010_; 
v___x_997_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_990_, v_fvarId_991_, v_a_993_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
if (lean_obj_tag(v_a_998_) == 1)
{
lean_object* v_val_1002_; lean_object* v___x_1004_; 
lean_dec(v_fvarId_991_);
v_val_1002_ = lean_ctor_get(v_a_998_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v_a_998_, 1);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_val_1002_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_val_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_del_object(v___x_1000_);
lean_dec(v_a_998_);
v___x_1006_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1007_ = l_Lean_MessageData_ofName(v_fvarId_991_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1008_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1011_, lean_object* v_fvarId_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
uint8_t v_pu_boxed_1018_; lean_object* v_res_1019_; 
v_pu_boxed_1018_ = lean_unbox(v_pu_1011_);
v_res_1019_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1018_, v_fvarId_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_lctx_1024_; lean_object* v_nextIdx_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1036_; 
v___x_1023_ = lean_st_ref_take(v_a_1021_);
v_lctx_1024_ = lean_ctor_get(v___x_1023_, 0);
v_nextIdx_1025_ = lean_ctor_get(v___x_1023_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1027_ = v___x_1023_;
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_nextIdx_1025_);
lean_inc(v_lctx_1024_);
lean_dec(v___x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_apply_1(v_f_1020_, v_lctx_1024_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_nextIdx_1025_);
v___x_1032_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_st_ref_put(v_a_1021_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1029_);
return v___x_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1037_, v_a_1038_);
lean_dec(v_a_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; lean_object* v_lctx_1048_; lean_object* v_nextIdx_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1060_; 
v___x_1047_ = lean_st_ref_take(v_a_1043_);
v_lctx_1048_ = lean_ctor_get(v___x_1047_, 0);
v_nextIdx_1049_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1060_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_nextIdx_1049_);
lean_inc(v_lctx_1048_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1060_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_apply_1(v_f_1041_, v_lctx_1048_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1054_);
v___x_1056_ = v___x_1051_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_nextIdx_1049_);
v___x_1056_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_st_ref_put(v_a_1043_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1053_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1068_, lean_object* v_decl_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v_lctx_1073_; lean_object* v_nextIdx_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1085_; 
v___x_1072_ = lean_st_ref_take(v_a_1070_);
v_lctx_1073_ = lean_ctor_get(v___x_1072_, 0);
v_nextIdx_1074_ = lean_ctor_get(v___x_1072_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1076_ = v___x_1072_;
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_nextIdx_1074_);
lean_inc(v_lctx_1073_);
lean_dec(v___x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1068_, v_lctx_1073_, v_decl_1069_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_nextIdx_1074_);
v___x_1081_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_st_ref_put(v_a_1070_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1078_);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1086_, lean_object* v_decl_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
uint8_t v_pu_boxed_1090_; lean_object* v_res_1091_; 
v_pu_boxed_1090_ = lean_unbox(v_pu_1086_);
v_res_1091_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1090_, v_decl_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_decl_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1092_, lean_object* v_decl_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1092_, v_decl_1093_, v_a_1095_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1100_, lean_object* v_decl_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
uint8_t v_pu_boxed_1107_; lean_object* v_res_1108_; 
v_pu_boxed_1107_ = lean_unbox(v_pu_1100_);
v_res_1108_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1107_, v_decl_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_decl_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1109_, lean_object* v_decl_1110_, uint8_t v_recursive_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_lctx_1115_; lean_object* v_nextIdx_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1127_; 
v___x_1114_ = lean_st_ref_take(v_a_1112_);
v_lctx_1115_ = lean_ctor_get(v___x_1114_, 0);
v_nextIdx_1116_ = lean_ctor_get(v___x_1114_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1118_ = v___x_1114_;
v_isShared_1119_ = v_isSharedCheck_1127_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_nextIdx_1116_);
lean_inc(v_lctx_1115_);
lean_dec(v___x_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1127_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1109_, v_lctx_1115_, v_decl_1110_, v_recursive_1111_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_nextIdx_1116_);
v___x_1123_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_st_ref_put(v_a_1112_, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1120_);
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1128_, lean_object* v_decl_1129_, lean_object* v_recursive_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
uint8_t v_pu_boxed_1133_; uint8_t v_recursive_boxed_1134_; lean_object* v_res_1135_; 
v_pu_boxed_1133_ = lean_unbox(v_pu_1128_);
v_recursive_boxed_1134_ = lean_unbox(v_recursive_1130_);
v_res_1135_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1133_, v_decl_1129_, v_recursive_boxed_1134_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_decl_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1136_, lean_object* v_decl_1137_, uint8_t v_recursive_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1136_, v_decl_1137_, v_recursive_1138_, v_a_1140_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1145_, lean_object* v_decl_1146_, lean_object* v_recursive_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
uint8_t v_pu_boxed_1153_; uint8_t v_recursive_boxed_1154_; lean_object* v_res_1155_; 
v_pu_boxed_1153_ = lean_unbox(v_pu_1145_);
v_recursive_boxed_1154_ = lean_unbox(v_recursive_1147_);
v_res_1155_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1153_, v_decl_1146_, v_recursive_boxed_1154_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec_ref(v_decl_1146_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1156_, lean_object* v_code_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v_lctx_1161_; lean_object* v_nextIdx_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1173_; 
v___x_1160_ = lean_st_ref_take(v_a_1158_);
v_lctx_1161_ = lean_ctor_get(v___x_1160_, 0);
v_nextIdx_1162_ = lean_ctor_get(v___x_1160_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1164_ = v___x_1160_;
v_isShared_1165_ = v_isSharedCheck_1173_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_nextIdx_1162_);
lean_inc(v_lctx_1161_);
lean_dec(v___x_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1173_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1156_, v_code_1157_, v_lctx_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_nextIdx_1162_);
v___x_1169_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_st_ref_put(v_a_1158_, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1166_);
return v___x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1174_, lean_object* v_code_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v_pu_boxed_1178_; lean_object* v_res_1179_; 
v_pu_boxed_1178_ = lean_unbox(v_pu_1174_);
v_res_1179_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1178_, v_code_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_code_1175_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1180_, lean_object* v_code_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1180_, v_code_1181_, v_a_1183_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1188_, lean_object* v_code_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
uint8_t v_pu_boxed_1195_; lean_object* v_res_1196_; 
v_pu_boxed_1195_ = lean_unbox(v_pu_1188_);
v_res_1196_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1195_, v_code_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec_ref(v_code_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1197_, lean_object* v_param_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_lctx_1202_; lean_object* v_nextIdx_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1214_; 
v___x_1201_ = lean_st_ref_take(v_a_1199_);
v_lctx_1202_ = lean_ctor_get(v___x_1201_, 0);
v_nextIdx_1203_ = lean_ctor_get(v___x_1201_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_nextIdx_1203_);
lean_inc(v_lctx_1202_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1197_, v_lctx_1202_, v_param_1198_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_nextIdx_1203_);
v___x_1210_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_st_ref_put(v_a_1199_, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1207_);
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1215_, lean_object* v_param_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
uint8_t v_pu_boxed_1219_; lean_object* v_res_1220_; 
v_pu_boxed_1219_ = lean_unbox(v_pu_1215_);
v_res_1220_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1219_, v_param_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_param_1216_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1221_, lean_object* v_param_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1221_, v_param_1222_, v_a_1224_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1229_, lean_object* v_param_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
uint8_t v_pu_boxed_1236_; lean_object* v_res_1237_; 
v_pu_boxed_1236_ = lean_unbox(v_pu_1229_);
v_res_1237_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1236_, v_param_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec_ref(v_param_1230_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1238_, lean_object* v_params_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v_lctx_1243_; lean_object* v_nextIdx_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1255_; 
v___x_1242_ = lean_st_ref_take(v_a_1240_);
v_lctx_1243_ = lean_ctor_get(v___x_1242_, 0);
v_nextIdx_1244_ = lean_ctor_get(v___x_1242_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1246_ = v___x_1242_;
v_isShared_1247_ = v_isSharedCheck_1255_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_nextIdx_1244_);
lean_inc(v_lctx_1243_);
lean_dec(v___x_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1255_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1238_, v_lctx_1243_, v_params_1239_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1249_);
v___x_1251_ = v___x_1246_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_nextIdx_1244_);
v___x_1251_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_st_ref_put(v_a_1240_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1248_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1256_, lean_object* v_params_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
uint8_t v_pu_boxed_1260_; lean_object* v_res_1261_; 
v_pu_boxed_1260_ = lean_unbox(v_pu_1256_);
v_res_1261_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1260_, v_params_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_params_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1262_, lean_object* v_params_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1262_, v_params_1263_, v_a_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1270_, lean_object* v_params_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
uint8_t v_pu_boxed_1277_; lean_object* v_res_1278_; 
v_pu_boxed_1277_ = lean_unbox(v_pu_1270_);
v_res_1278_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1277_, v_params_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec_ref(v_params_1271_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1279_, lean_object* v_decl_1280_, lean_object* v_a_1281_){
_start:
{
switch(lean_obj_tag(v_decl_1280_))
{
case 0:
{
lean_object* v_decl_1283_; lean_object* v___x_1284_; 
v_decl_1283_ = lean_ctor_get(v_decl_1280_, 0);
v___x_1284_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1279_, v_decl_1283_, v_a_1281_);
return v___x_1284_;
}
case 1:
{
lean_object* v_decl_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
v_decl_1285_ = lean_ctor_get(v_decl_1280_, 0);
v___x_1286_ = 1;
v___x_1287_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1279_, v_decl_1285_, v___x_1286_, v_a_1281_);
return v___x_1287_;
}
case 2:
{
lean_object* v_decl_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; 
v_decl_1288_ = lean_ctor_get(v_decl_1280_, 0);
v___x_1289_ = 1;
v___x_1290_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1279_, v_decl_1288_, v___x_1289_, v_a_1281_);
return v___x_1290_;
}
default: 
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1293_, lean_object* v_decl_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
uint8_t v_pu_boxed_1297_; lean_object* v_res_1298_; 
v_pu_boxed_1297_ = lean_unbox(v_pu_1293_);
v_res_1298_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1297_, v_decl_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_decl_1294_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1299_, lean_object* v_decl_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1299_, v_decl_1300_, v_a_1302_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1307_, lean_object* v_decl_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
uint8_t v_pu_boxed_1314_; lean_object* v_res_1315_; 
v_pu_boxed_1314_ = lean_unbox(v_pu_1307_);
v_res_1315_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1314_, v_decl_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec_ref(v_decl_1308_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1316_, lean_object* v_as_1317_, size_t v_i_1318_, size_t v_stop_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_eq(v_i_1318_, v_stop_1319_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_array_uget_borrowed(v_as_1317_, v_i_1318_);
v___x_1325_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1316_, v___x_1324_, v___y_1321_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; size_t v___x_1327_; size_t v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_add(v_i_1318_, v___x_1327_);
v_i_1318_ = v___x_1328_;
v_b_1320_ = v_a_1326_;
goto _start;
}
else
{
return v___x_1325_;
}
}
else
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_b_1320_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1331_, lean_object* v_as_1332_, lean_object* v_i_1333_, lean_object* v_stop_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v_pu_boxed_1338_; size_t v_i_boxed_1339_; size_t v_stop_boxed_1340_; lean_object* v_res_1341_; 
v_pu_boxed_1338_ = lean_unbox(v_pu_1331_);
v_i_boxed_1339_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_stop_boxed_1340_ = lean_unbox_usize(v_stop_1334_);
lean_dec(v_stop_1334_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1338_, v_as_1332_, v_i_boxed_1339_, v_stop_boxed_1340_, v_b_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v_as_1332_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1342_, lean_object* v_decls_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_array_get_size(v_decls_1343_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
return v___x_1353_;
}
else
{
size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1350_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1342_, v_decls_1343_, v___x_1354_, v___x_1355_, v___x_1351_, v_a_1345_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1357_, lean_object* v_decls_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
uint8_t v_pu_boxed_1364_; lean_object* v_res_1365_; 
v_pu_boxed_1364_ = lean_unbox(v_pu_1357_);
v_res_1365_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1364_, v_decls_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec_ref(v_decls_1358_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1366_, lean_object* v_as_1367_, size_t v_i_1368_, size_t v_stop_1369_, lean_object* v_b_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1366_, v_as_1367_, v_i_1368_, v_stop_1369_, v_b_1370_, v___y_1372_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1377_, lean_object* v_as_1378_, lean_object* v_i_1379_, lean_object* v_stop_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_pu_boxed_1387_; size_t v_i_boxed_1388_; size_t v_stop_boxed_1389_; lean_object* v_res_1390_; 
v_pu_boxed_1387_ = lean_unbox(v_pu_1377_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_stop_boxed_1389_ = lean_unbox_usize(v_stop_1380_);
lean_dec(v_stop_1380_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1387_, v_as_1378_, v_i_boxed_1388_, v_stop_boxed_1389_, v_b_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_as_1378_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1391_, lean_object* v_v_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
if (lean_obj_tag(v_v_1392_) == 0)
{
lean_object* v_code_1398_; lean_object* v___x_1399_; 
v_code_1398_ = lean_ctor_get(v_v_1392_, 0);
lean_inc_ref(v_code_1398_);
lean_dec_ref_known(v_v_1392_, 1);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
v___x_1399_ = lean_apply_6(v_f_1391_, v_code_1398_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1399_;
}
else
{
lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_f_1391_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_v_1392_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_v_1392_, 0);
lean_dec(v_unused_1408_);
v___x_1401_ = v_v_1392_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_dec(v_v_1392_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(0);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1409_, lean_object* v_v_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1409_, v_v_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1417_, lean_object* v_f_1418_, lean_object* v_v_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1418_, v_v_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1426_, lean_object* v_f_1427_, lean_object* v_v_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
uint8_t v_pu_boxed_1434_; lean_object* v_res_1435_; 
v_pu_boxed_1434_ = lean_unbox(v_pu_1426_);
v_res_1435_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1434_, v_f_1427_, v_v_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1436_, lean_object* v_decl_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_toSignature_1443_; lean_object* v_value_1444_; lean_object* v_params_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_toSignature_1443_ = lean_ctor_get(v_decl_1437_, 0);
lean_inc_ref(v_toSignature_1443_);
v_value_1444_ = lean_ctor_get(v_decl_1437_, 1);
lean_inc_ref(v_value_1444_);
lean_dec_ref(v_decl_1437_);
v_params_1445_ = lean_ctor_get(v_toSignature_1443_, 3);
lean_inc_ref(v_params_1445_);
lean_dec_ref(v_toSignature_1443_);
v___x_1446_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1436_, v_params_1445_, v_a_1439_);
lean_dec_ref(v_params_1445_);
lean_dec_ref(v___x_1446_);
v___x_1447_ = lean_box(v_pu_1436_);
v___x_1448_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1448_, v_value_1444_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1450_, lean_object* v_decl_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
uint8_t v_pu_boxed_1457_; lean_object* v_res_1458_; 
v_pu_boxed_1457_ = lean_unbox(v_pu_1450_);
v_res_1458_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1457_, v_decl_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1459_, lean_object* v_decl_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1459_, v_decl_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1467_, lean_object* v_decl_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
uint8_t v_pu_boxed_1474_; lean_object* v_res_1475_; 
v_pu_boxed_1474_ = lean_unbox(v_pu_1467_);
v_res_1475_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1474_, v_decl_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = l_Lean_instInhabitedExpr;
v___x_1478_ = lean_panic_fn_borrowed(v___x_1477_, v_msg_1476_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1483_ = lean_unsigned_to_nat(20u);
v___x_1484_ = lean_unsigned_to_nat(215u);
v___x_1485_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1486_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1487_ = l_mkPanicMessageWithDecl(v___x_1486_, v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1488_, lean_object* v_s_1489_, uint8_t v_translator_1490_, lean_object* v_e_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = l_Lean_Expr_hasFVar(v_e_1491_);
if (v___x_1492_ == 0)
{
return v_e_1491_;
}
else
{
switch(lean_obj_tag(v_e_1491_))
{
case 1:
{
lean_object* v_fvarId_1493_; lean_object* v___x_1494_; 
v_fvarId_1493_ = lean_ctor_get(v_e_1491_, 0);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1489_, v_fvarId_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
return v_e_1491_;
}
else
{
lean_object* v_val_1495_; 
lean_dec_ref_known(v_e_1491_, 1);
v_val_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v___x_1494_, 1);
switch(lean_obj_tag(v_val_1495_))
{
case 0:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1496_;
}
case 1:
{
if (v_translator_1490_ == 0)
{
lean_object* v_fvarId_1497_; lean_object* v___x_1498_; 
v_fvarId_1497_ = lean_ctor_get(v_val_1495_, 0);
lean_inc(v_fvarId_1497_);
lean_dec_ref_known(v_val_1495_, 1);
v___x_1498_ = l_Lean_Expr_fvar___override(v_fvarId_1497_);
v_e_1491_ = v___x_1498_;
goto _start;
}
else
{
lean_object* v_fvarId_1500_; lean_object* v___x_1501_; 
v_fvarId_1500_ = lean_ctor_get(v_val_1495_, 0);
lean_inc(v_fvarId_1500_);
lean_dec_ref_known(v_val_1495_, 1);
v___x_1501_ = l_Lean_Expr_fvar___override(v_fvarId_1500_);
return v___x_1501_;
}
}
default: 
{
if (v_translator_1490_ == 0)
{
lean_object* v_expr_1502_; 
v_expr_1502_ = lean_ctor_get(v_val_1495_, 0);
lean_inc_ref(v_expr_1502_);
lean_dec_ref_known(v_val_1495_, 1);
v_e_1491_ = v_expr_1502_;
goto _start;
}
else
{
lean_object* v_expr_1504_; 
v_expr_1504_ = lean_ctor_get(v_val_1495_, 0);
lean_inc_ref(v_expr_1504_);
lean_dec_ref_known(v_val_1495_, 1);
return v_expr_1504_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1505_; lean_object* v_arg_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_fn_1505_ = lean_ctor_get(v_e_1491_, 0);
v_arg_1506_ = lean_ctor_get(v_e_1491_, 1);
lean_inc_ref(v_fn_1505_);
v___x_1507_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1488_, v_s_1489_, v_translator_1490_, v_fn_1505_);
lean_inc_ref(v_arg_1506_);
v___x_1508_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_arg_1506_);
v___x_1509_ = lean_ptr_addr(v_fn_1505_);
v___x_1510_ = lean_ptr_addr(v___x_1507_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref_known(v_e_1491_, 2);
v___x_1512_ = l_Lean_Expr_app___override(v___x_1507_, v___x_1508_);
v___x_1513_ = l_Lean_Expr_headBeta(v___x_1512_);
return v___x_1513_;
}
else
{
size_t v___x_1514_; size_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = lean_ptr_addr(v_arg_1506_);
v___x_1515_ = lean_ptr_addr(v___x_1508_);
v___x_1516_ = lean_usize_dec_eq(v___x_1514_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref_known(v_e_1491_, 2);
v___x_1517_ = l_Lean_Expr_app___override(v___x_1507_, v___x_1508_);
v___x_1518_ = l_Lean_Expr_headBeta(v___x_1517_);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; 
lean_dec_ref(v___x_1508_);
lean_dec_ref(v___x_1507_);
v___x_1519_ = l_Lean_Expr_headBeta(v_e_1491_);
return v___x_1519_;
}
}
}
case 6:
{
lean_object* v_binderName_1520_; lean_object* v_binderType_1521_; lean_object* v_body_1522_; uint8_t v_binderInfo_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v_binderName_1520_ = lean_ctor_get(v_e_1491_, 0);
v_binderType_1521_ = lean_ctor_get(v_e_1491_, 1);
v_body_1522_ = lean_ctor_get(v_e_1491_, 2);
v_binderInfo_1523_ = lean_ctor_get_uint8(v_e_1491_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1521_);
v___x_1524_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_binderType_1521_);
lean_inc_ref(v_body_1522_);
v___x_1525_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_body_1522_);
v___x_1526_ = lean_ptr_addr(v_binderType_1521_);
v___x_1527_ = lean_ptr_addr(v___x_1524_);
v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_binderName_1520_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1529_ = l_Lean_Expr_lam___override(v_binderName_1520_, v___x_1524_, v___x_1525_, v_binderInfo_1523_);
return v___x_1529_;
}
else
{
size_t v___x_1530_; size_t v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = lean_ptr_addr(v_body_1522_);
v___x_1531_ = lean_ptr_addr(v___x_1525_);
v___x_1532_ = lean_usize_dec_eq(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_inc(v_binderName_1520_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1533_ = l_Lean_Expr_lam___override(v_binderName_1520_, v___x_1524_, v___x_1525_, v_binderInfo_1523_);
return v___x_1533_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1523_, v_binderInfo_1523_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_binderName_1520_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1535_ = l_Lean_Expr_lam___override(v_binderName_1520_, v___x_1524_, v___x_1525_, v_binderInfo_1523_);
return v___x_1535_;
}
else
{
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1524_);
return v_e_1491_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1536_; lean_object* v_binderType_1537_; lean_object* v_body_1538_; uint8_t v_binderInfo_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; uint8_t v___x_1544_; 
v_binderName_1536_ = lean_ctor_get(v_e_1491_, 0);
v_binderType_1537_ = lean_ctor_get(v_e_1491_, 1);
v_body_1538_ = lean_ctor_get(v_e_1491_, 2);
v_binderInfo_1539_ = lean_ctor_get_uint8(v_e_1491_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1537_);
v___x_1540_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_binderType_1537_);
lean_inc_ref(v_body_1538_);
v___x_1541_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_body_1538_);
v___x_1542_ = lean_ptr_addr(v_binderType_1537_);
v___x_1543_ = lean_ptr_addr(v___x_1540_);
v___x_1544_ = lean_usize_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_inc(v_binderName_1536_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1545_ = l_Lean_Expr_forallE___override(v_binderName_1536_, v___x_1540_, v___x_1541_, v_binderInfo_1539_);
return v___x_1545_;
}
else
{
size_t v___x_1546_; size_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_ptr_addr(v_body_1538_);
v___x_1547_ = lean_ptr_addr(v___x_1541_);
v___x_1548_ = lean_usize_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_binderName_1536_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1549_ = l_Lean_Expr_forallE___override(v_binderName_1536_, v___x_1540_, v___x_1541_, v_binderInfo_1539_);
return v___x_1549_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1539_, v_binderInfo_1539_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_inc(v_binderName_1536_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1551_ = l_Lean_Expr_forallE___override(v_binderName_1536_, v___x_1540_, v___x_1541_, v_binderInfo_1539_);
return v___x_1551_;
}
else
{
lean_dec_ref(v___x_1541_);
lean_dec_ref(v___x_1540_);
return v_e_1491_;
}
}
}
}
case 8:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec_ref_known(v_e_1491_, 4);
v___x_1552_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1553_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1552_);
return v___x_1553_;
}
case 10:
{
lean_object* v_data_1554_; lean_object* v_expr_1555_; lean_object* v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; uint8_t v___x_1559_; 
v_data_1554_ = lean_ctor_get(v_e_1491_, 0);
v_expr_1555_ = lean_ctor_get(v_e_1491_, 1);
lean_inc_ref(v_expr_1555_);
v___x_1556_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_expr_1555_);
v___x_1557_ = lean_ptr_addr(v_expr_1555_);
v___x_1558_ = lean_ptr_addr(v___x_1556_);
v___x_1559_ = lean_usize_dec_eq(v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_inc(v_data_1554_);
lean_dec_ref_known(v_e_1491_, 2);
v___x_1560_ = l_Lean_Expr_mdata___override(v_data_1554_, v___x_1556_);
return v___x_1560_;
}
else
{
lean_dec_ref(v___x_1556_);
return v_e_1491_;
}
}
case 11:
{
lean_object* v_typeName_1561_; lean_object* v_idx_1562_; lean_object* v_struct_1563_; lean_object* v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; uint8_t v___x_1567_; 
v_typeName_1561_ = lean_ctor_get(v_e_1491_, 0);
v_idx_1562_ = lean_ctor_get(v_e_1491_, 1);
v_struct_1563_ = lean_ctor_get(v_e_1491_, 2);
lean_inc_ref(v_struct_1563_);
v___x_1564_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1488_, v_s_1489_, v_translator_1490_, v_struct_1563_);
v___x_1565_ = lean_ptr_addr(v_struct_1563_);
v___x_1566_ = lean_ptr_addr(v___x_1564_);
v___x_1567_ = lean_usize_dec_eq(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_inc(v_idx_1562_);
lean_inc(v_typeName_1561_);
lean_dec_ref_known(v_e_1491_, 3);
v___x_1568_ = l_Lean_Expr_proj___override(v_typeName_1561_, v_idx_1562_, v___x_1564_);
return v___x_1568_;
}
else
{
lean_dec_ref(v___x_1564_);
return v_e_1491_;
}
}
default: 
{
return v_e_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1569_, lean_object* v_s_1570_, uint8_t v_translator_1571_, lean_object* v_e_1572_){
_start:
{
if (lean_obj_tag(v_e_1572_) == 5)
{
lean_object* v_fn_1573_; lean_object* v_arg_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; size_t v___x_1577_; size_t v___x_1578_; uint8_t v___x_1579_; 
v_fn_1573_ = lean_ctor_get(v_e_1572_, 0);
v_arg_1574_ = lean_ctor_get(v_e_1572_, 1);
lean_inc_ref(v_fn_1573_);
v___x_1575_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1569_, v_s_1570_, v_translator_1571_, v_fn_1573_);
lean_inc_ref(v_arg_1574_);
v___x_1576_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1569_, v_s_1570_, v_translator_1571_, v_arg_1574_);
v___x_1577_ = lean_ptr_addr(v_fn_1573_);
v___x_1578_ = lean_ptr_addr(v___x_1575_);
v___x_1579_ = lean_usize_dec_eq(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref_known(v_e_1572_, 2);
v___x_1580_ = l_Lean_Expr_app___override(v___x_1575_, v___x_1576_);
return v___x_1580_;
}
else
{
size_t v___x_1581_; size_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1581_ = lean_ptr_addr(v_arg_1574_);
v___x_1582_ = lean_ptr_addr(v___x_1576_);
v___x_1583_ = lean_usize_dec_eq(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref_known(v_e_1572_, 2);
v___x_1584_ = l_Lean_Expr_app___override(v___x_1575_, v___x_1576_);
return v___x_1584_;
}
else
{
lean_dec_ref(v___x_1576_);
lean_dec_ref(v___x_1575_);
return v_e_1572_;
}
}
}
else
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1569_, v_s_1570_, v_translator_1571_, v_e_1572_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1586_, lean_object* v_s_1587_, lean_object* v_translator_1588_, lean_object* v_e_1589_){
_start:
{
uint8_t v_pu_boxed_1590_; uint8_t v_translator_boxed_1591_; lean_object* v_res_1592_; 
v_pu_boxed_1590_ = lean_unbox(v_pu_1586_);
v_translator_boxed_1591_ = lean_unbox(v_translator_1588_);
v_res_1592_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1590_, v_s_1587_, v_translator_boxed_1591_, v_e_1589_);
lean_dec_ref(v_s_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1593_, lean_object* v_s_1594_, lean_object* v_translator_1595_, lean_object* v_e_1596_){
_start:
{
uint8_t v_pu_boxed_1597_; uint8_t v_translator_boxed_1598_; lean_object* v_res_1599_; 
v_pu_boxed_1597_ = lean_unbox(v_pu_1593_);
v_translator_boxed_1598_ = lean_unbox(v_translator_1595_);
v_res_1599_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1597_, v_s_1594_, v_translator_boxed_1598_, v_e_1596_);
lean_dec_ref(v_s_1594_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1600_, lean_object* v_s_1601_, lean_object* v_e_1602_, uint8_t v_translator_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1600_, v_s_1601_, v_translator_1603_, v_e_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1605_, lean_object* v_s_1606_, lean_object* v_e_1607_, lean_object* v_translator_1608_){
_start:
{
uint8_t v_pu_boxed_1609_; uint8_t v_translator_boxed_1610_; lean_object* v_res_1611_; 
v_pu_boxed_1609_ = lean_unbox(v_pu_1605_);
v_translator_boxed_1610_ = lean_unbox(v_translator_1608_);
v_res_1611_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1609_, v_s_1606_, v_e_1607_, v_translator_boxed_1610_);
lean_dec_ref(v_s_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_tag_nat(v_x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl___boxed(lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(v_x_1614_);
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
v___x_1782_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1763_, v___x_1781_);
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
v___x_1788_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1763_, v_fvarId_1786_, v___x_1787_);
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
v___x_1792_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1763_, v___x_1791_);
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
v___x_1806_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1763_, v_n_1802_, v_fvarId_1805_);
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
v___x_1815_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1763_, v_fvarId_1813_, v_i_1809_, v_updateHeader_1810_, v___x_1814_);
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
v___x_1821_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1763_, v_ty_1817_, v_fvarId_1820_);
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
v___x_1826_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1763_, v_fvarId_1825_);
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
v___x_1831_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1763_, v_fvarId_1830_);
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
v___x_1774_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1763_, v___x_1773_);
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
lean_object* v___x_2227_; lean_object* v_nextIdx_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_lctx_2231_; lean_object* v_nextIdx_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2243_; 
v___x_2227_ = lean_st_ref_get(v_a_2225_);
v_nextIdx_2228_ = lean_ctor_get(v___x_2227_, 1);
lean_inc(v_nextIdx_2228_);
lean_dec(v___x_2227_);
v___x_2229_ = l_Lean_Name_num___override(v_binderName_2224_, v_nextIdx_2228_);
v___x_2230_ = lean_st_ref_take(v_a_2225_);
v_lctx_2231_ = lean_ctor_get(v___x_2230_, 0);
v_nextIdx_2232_ = lean_ctor_get(v___x_2230_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2234_ = v___x_2230_;
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_nextIdx_2232_);
lean_inc(v_lctx_2231_);
lean_dec(v___x_2230_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_add(v_nextIdx_2232_, v___x_2236_);
lean_dec(v_nextIdx_2232_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_lctx_2231_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_st_ref_put(v_a_2225_, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2229_);
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
lean_object* v___x_2292_; lean_object* v_ngen_2293_; lean_object* v_namePrefix_2294_; lean_object* v_idx_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2325_; 
v___x_2292_ = lean_st_ref_get(v___y_2290_);
v_ngen_2293_ = lean_ctor_get(v___x_2292_, 2);
lean_inc_ref(v_ngen_2293_);
lean_dec(v___x_2292_);
v_namePrefix_2294_ = lean_ctor_get(v_ngen_2293_, 0);
v_idx_2295_ = lean_ctor_get(v_ngen_2293_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_ngen_2293_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2297_ = v_ngen_2293_;
v_isShared_2298_ = v_isSharedCheck_2325_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_idx_2295_);
lean_inc(v_namePrefix_2294_);
lean_dec(v_ngen_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2325_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_r_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_inc(v_idx_2295_);
lean_inc(v_namePrefix_2294_);
v_r_2299_ = l_Lean_Name_num___override(v_namePrefix_2294_, v_idx_2295_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_nat_add(v_idx_2295_, v___x_2300_);
lean_dec(v_idx_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2301_);
v___x_2303_ = v___x_2297_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_namePrefix_2294_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; lean_object* v_env_2305_; lean_object* v_nextMacroScope_2306_; lean_object* v_auxDeclNGen_2307_; lean_object* v_traceState_2308_; lean_object* v_cache_2309_; lean_object* v_recordedDeps_2310_; lean_object* v_messages_2311_; lean_object* v_infoState_2312_; lean_object* v_snapshotTasks_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v___x_2304_ = lean_st_ref_take(v___y_2290_);
v_env_2305_ = lean_ctor_get(v___x_2304_, 0);
v_nextMacroScope_2306_ = lean_ctor_get(v___x_2304_, 1);
v_auxDeclNGen_2307_ = lean_ctor_get(v___x_2304_, 3);
v_traceState_2308_ = lean_ctor_get(v___x_2304_, 4);
v_cache_2309_ = lean_ctor_get(v___x_2304_, 5);
v_recordedDeps_2310_ = lean_ctor_get(v___x_2304_, 6);
v_messages_2311_ = lean_ctor_get(v___x_2304_, 7);
v_infoState_2312_ = lean_ctor_get(v___x_2304_, 8);
v_snapshotTasks_2313_ = lean_ctor_get(v___x_2304_, 9);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2304_, 2);
lean_dec(v_unused_2323_);
v___x_2315_ = v___x_2304_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snapshotTasks_2313_);
lean_inc(v_infoState_2312_);
lean_inc(v_messages_2311_);
lean_inc(v_recordedDeps_2310_);
lean_inc(v_cache_2309_);
lean_inc(v_traceState_2308_);
lean_inc(v_auxDeclNGen_2307_);
lean_inc(v_nextMacroScope_2306_);
lean_inc(v_env_2305_);
lean_dec(v___x_2304_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 2, v___x_2303_);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_env_2305_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_nextMacroScope_2306_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_auxDeclNGen_2307_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_traceState_2308_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_cache_2309_);
lean_ctor_set(v_reuseFailAlloc_2321_, 6, v_recordedDeps_2310_);
lean_ctor_set(v_reuseFailAlloc_2321_, 7, v_messages_2311_);
lean_ctor_set(v_reuseFailAlloc_2321_, 8, v_infoState_2312_);
lean_ctor_set(v_reuseFailAlloc_2321_, 9, v_snapshotTasks_2313_);
v___x_2318_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_st_ref_put(v___y_2290_, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_r_2299_);
return v___x_2320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2326_);
lean_dec(v___y_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v___x_2334_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2332_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2352_, lean_object* v_binderName_2353_, lean_object* v_type_2354_, uint8_t v_borrow_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2385_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2364_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2353_, v___x_2363_, v_a_2357_);
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2385_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2385_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_lctx_2371_; lean_object* v_nextIdx_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2384_; 
v___x_2369_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2369_, 0, v_a_2362_);
lean_ctor_set(v___x_2369_, 1, v_a_2365_);
lean_ctor_set(v___x_2369_, 2, v_type_2354_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*3, v_borrow_2355_);
v___x_2370_ = lean_st_ref_take(v_a_2357_);
v_lctx_2371_ = lean_ctor_get(v___x_2370_, 0);
v_nextIdx_2372_ = lean_ctor_get(v___x_2370_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2374_ = v___x_2370_;
v_isShared_2375_ = v_isSharedCheck_2384_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_nextIdx_2372_);
lean_inc(v_lctx_2371_);
lean_dec(v___x_2370_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2384_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_inc_ref(v___x_2369_);
v___x_2376_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2352_, v_lctx_2371_, v___x_2369_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_nextIdx_2372_);
v___x_2378_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2379_ = lean_st_ref_put(v_a_2357_, v___x_2378_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2369_);
v___x_2381_ = v___x_2367_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2369_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v_type_2354_);
lean_dec(v_binderName_2353_);
v_a_2386_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2361_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2361_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2394_, lean_object* v_binderName_2395_, lean_object* v_type_2396_, lean_object* v_borrow_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
uint8_t v_pu_boxed_2403_; uint8_t v_borrow_boxed_2404_; lean_object* v_res_2405_; 
v_pu_boxed_2403_ = lean_unbox(v_pu_2394_);
v_borrow_boxed_2404_ = lean_unbox(v_borrow_2397_);
v_res_2405_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2403_, v_binderName_2395_, v_type_2396_, v_borrow_boxed_2404_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2421_, lean_object* v_binderName_2422_, lean_object* v_type_2423_, lean_object* v_value_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2454_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2432_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2433_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2422_, v___x_2432_, v_a_2426_);
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2454_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2454_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_lctx_2440_; lean_object* v_nextIdx_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2453_; 
v___x_2438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2438_, 0, v_a_2431_);
lean_ctor_set(v___x_2438_, 1, v_a_2434_);
lean_ctor_set(v___x_2438_, 2, v_type_2423_);
lean_ctor_set(v___x_2438_, 3, v_value_2424_);
v___x_2439_ = lean_st_ref_take(v_a_2426_);
v_lctx_2440_ = lean_ctor_get(v___x_2439_, 0);
v_nextIdx_2441_ = lean_ctor_get(v___x_2439_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2443_ = v___x_2439_;
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_nextIdx_2441_);
lean_inc(v_lctx_2440_);
lean_dec(v___x_2439_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_inc_ref(v___x_2438_);
v___x_2445_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2421_, v_lctx_2440_, v___x_2438_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_nextIdx_2441_);
v___x_2447_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_st_ref_put(v_a_2426_, v___x_2447_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2450_ = v___x_2436_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2438_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_value_2424_);
lean_dec_ref(v_type_2423_);
lean_dec(v_binderName_2422_);
v_a_2455_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2430_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2430_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2463_, lean_object* v_binderName_2464_, lean_object* v_type_2465_, lean_object* v_value_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
uint8_t v_pu_boxed_2472_; lean_object* v_res_2473_; 
v_pu_boxed_2472_ = lean_unbox(v_pu_2463_);
v_res_2473_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2472_, v_binderName_2464_, v_type_2465_, v_value_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2477_, lean_object* v_binderName_2478_, lean_object* v_type_2479_, lean_object* v_params_2480_, lean_object* v_value_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2511_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2490_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2478_, v___x_2489_, v_a_2483_);
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2511_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2511_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v_lctx_2497_; lean_object* v_nextIdx_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2510_; 
v___x_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2488_);
lean_ctor_set(v___x_2495_, 1, v_a_2491_);
lean_ctor_set(v___x_2495_, 2, v_params_2480_);
lean_ctor_set(v___x_2495_, 3, v_type_2479_);
lean_ctor_set(v___x_2495_, 4, v_value_2481_);
v___x_2496_ = lean_st_ref_take(v_a_2483_);
v_lctx_2497_ = lean_ctor_get(v___x_2496_, 0);
v_nextIdx_2498_ = lean_ctor_get(v___x_2496_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2500_ = v___x_2496_;
v_isShared_2501_ = v_isSharedCheck_2510_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_nextIdx_2498_);
lean_inc(v_lctx_2497_);
lean_dec(v___x_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2510_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_inc_ref(v___x_2495_);
v___x_2502_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2477_, v_lctx_2497_, v___x_2495_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_nextIdx_2498_);
v___x_2504_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = lean_st_ref_put(v_a_2483_, v___x_2504_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2495_);
v___x_2507_ = v___x_2493_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2495_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v_value_2481_);
lean_dec_ref(v_params_2480_);
lean_dec_ref(v_type_2479_);
lean_dec(v_binderName_2478_);
v_a_2512_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2487_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2487_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2520_, lean_object* v_binderName_2521_, lean_object* v_type_2522_, lean_object* v_params_2523_, lean_object* v_value_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
uint8_t v_pu_boxed_2530_; lean_object* v_res_2531_; 
v_pu_boxed_2530_ = lean_unbox(v_pu_2520_);
v_res_2531_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2530_, v_binderName_2521_, v_type_2522_, v_params_2523_, v_value_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_a_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2538_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2539_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2538_, v_a_2534_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2539_);
v___x_2541_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2542_ = lean_box(1);
v___x_2543_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2532_, v_a_2540_, v___x_2541_, v___x_2542_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
uint8_t v_pu_boxed_2550_; lean_object* v_res_2551_; 
v_pu_boxed_2550_ = lean_unbox(v_pu_2544_);
v_res_2551_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2550_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2569_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2569_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2569_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_fvarId_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v_fvarId_2563_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_fvarId_2563_);
v___x_2564_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_fvarId_2563_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2559_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2565_);
v___x_2567_ = v___x_2561_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v_a_2570_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2558_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2558_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
uint8_t v_pu_boxed_2584_; lean_object* v_res_2585_; 
v_pu_boxed_2584_ = lean_unbox(v_pu_2578_);
v_res_2585_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2584_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2586_, lean_object* v_p_2587_, lean_object* v_type_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_fvarId_2591_; lean_object* v_binderName_2592_; lean_object* v_type_2593_; uint8_t v_borrow_2594_; size_t v___x_2595_; size_t v___x_2596_; uint8_t v___x_2597_; 
v_fvarId_2591_ = lean_ctor_get(v_p_2587_, 0);
v_binderName_2592_ = lean_ctor_get(v_p_2587_, 1);
v_type_2593_ = lean_ctor_get(v_p_2587_, 2);
v_borrow_2594_ = lean_ctor_get_uint8(v_p_2587_, sizeof(void*)*3);
v___x_2595_ = lean_ptr_addr(v_type_2588_);
v___x_2596_ = lean_ptr_addr(v_type_2593_);
v___x_2597_ = lean_usize_dec_eq(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2617_; 
lean_inc(v_binderName_2592_);
lean_inc(v_fvarId_2591_);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_p_2587_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; lean_object* v_unused_2619_; lean_object* v_unused_2620_; 
v_unused_2618_ = lean_ctor_get(v_p_2587_, 2);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_p_2587_, 1);
lean_dec(v_unused_2619_);
v_unused_2620_ = lean_ctor_get(v_p_2587_, 0);
lean_dec(v_unused_2620_);
v___x_2599_ = v_p_2587_;
v_isShared_2600_ = v_isSharedCheck_2617_;
goto v_resetjp_2598_;
}
else
{
lean_dec(v_p_2587_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2617_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_p_2602_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 2, v_type_2588_);
v_p_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fvarId_2591_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_binderName_2592_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_type_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*3, v_borrow_2594_);
v_p_2602_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v_lctx_2604_; lean_object* v_nextIdx_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2615_; 
v___x_2603_ = lean_st_ref_take(v_a_2589_);
v_lctx_2604_ = lean_ctor_get(v___x_2603_, 0);
v_nextIdx_2605_ = lean_ctor_get(v___x_2603_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2607_ = v___x_2603_;
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_nextIdx_2605_);
lean_inc(v_lctx_2604_);
lean_dec(v___x_2603_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_inc_ref(v_p_2602_);
v___x_2609_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2586_, v_lctx_2604_, v_p_2602_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_nextIdx_2605_);
v___x_2611_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_st_ref_put(v_a_2589_, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_p_2602_);
return v___x_2613_;
}
}
}
}
}
else
{
lean_object* v___x_2621_; 
lean_dec_ref(v_type_2588_);
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_p_2587_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2622_, lean_object* v_p_2623_, lean_object* v_type_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
uint8_t v_pu_boxed_2627_; lean_object* v_res_2628_; 
v_pu_boxed_2627_ = lean_unbox(v_pu_2622_);
v_res_2628_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2627_, v_p_2623_, v_type_2624_, v_a_2625_);
lean_dec(v_a_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2629_, lean_object* v_p_2630_, lean_object* v_type_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2629_, v_p_2630_, v_type_2631_, v_a_2633_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2638_, lean_object* v_p_2639_, lean_object* v_type_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
uint8_t v_pu_boxed_2646_; lean_object* v_res_2647_; 
v_pu_boxed_2646_ = lean_unbox(v_pu_2638_);
v_res_2647_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2646_, v_p_2639_, v_type_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2648_, lean_object* v_p_2649_, uint8_t v_borrow_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_fvarId_2653_; lean_object* v_binderName_2654_; lean_object* v_type_2655_; uint8_t v_borrow_2656_; 
v_fvarId_2653_ = lean_ctor_get(v_p_2649_, 0);
v_binderName_2654_ = lean_ctor_get(v_p_2649_, 1);
v_type_2655_ = lean_ctor_get(v_p_2649_, 2);
v_borrow_2656_ = lean_ctor_get_uint8(v_p_2649_, sizeof(void*)*3);
if (v_borrow_2656_ == 0)
{
if (v_borrow_2650_ == 0)
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_p_2649_);
return v___x_2672_;
}
else
{
lean_inc_ref(v_type_2655_);
lean_inc(v_binderName_2654_);
lean_inc(v_fvarId_2653_);
lean_dec_ref(v_p_2649_);
goto v___jp_2657_;
}
}
else
{
if (v_borrow_2650_ == 0)
{
lean_inc_ref(v_type_2655_);
lean_inc(v_binderName_2654_);
lean_inc(v_fvarId_2653_);
lean_dec_ref(v_p_2649_);
goto v___jp_2657_;
}
else
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_p_2649_);
return v___x_2673_;
}
}
v___jp_2657_:
{
lean_object* v_p_2658_; lean_object* v___x_2659_; lean_object* v_lctx_2660_; lean_object* v_nextIdx_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2671_; 
v_p_2658_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2658_, 0, v_fvarId_2653_);
lean_ctor_set(v_p_2658_, 1, v_binderName_2654_);
lean_ctor_set(v_p_2658_, 2, v_type_2655_);
lean_ctor_set_uint8(v_p_2658_, sizeof(void*)*3, v_borrow_2650_);
v___x_2659_ = lean_st_ref_take(v_a_2651_);
v_lctx_2660_ = lean_ctor_get(v___x_2659_, 0);
v_nextIdx_2661_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2663_ = v___x_2659_;
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_nextIdx_2661_);
lean_inc(v_lctx_2660_);
lean_dec(v___x_2659_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_inc_ref(v_p_2658_);
v___x_2665_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2648_, v_lctx_2660_, v_p_2658_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2665_);
v___x_2667_ = v___x_2663_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_nextIdx_2661_);
v___x_2667_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_st_ref_put(v_a_2651_, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_p_2658_);
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2674_, lean_object* v_p_2675_, lean_object* v_borrow_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
uint8_t v_pu_boxed_2679_; uint8_t v_borrow_boxed_2680_; lean_object* v_res_2681_; 
v_pu_boxed_2679_ = lean_unbox(v_pu_2674_);
v_borrow_boxed_2680_ = lean_unbox(v_borrow_2676_);
v_res_2681_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2679_, v_p_2675_, v_borrow_boxed_2680_, v_a_2677_);
lean_dec(v_a_2677_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2682_, lean_object* v_p_2683_, uint8_t v_borrow_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2682_, v_p_2683_, v_borrow_2684_, v_a_2686_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2691_, lean_object* v_p_2692_, lean_object* v_borrow_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
uint8_t v_pu_boxed_2699_; uint8_t v_borrow_boxed_2700_; lean_object* v_res_2701_; 
v_pu_boxed_2699_ = lean_unbox(v_pu_2691_);
v_borrow_boxed_2700_ = lean_unbox(v_borrow_2693_);
v_res_2701_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2699_, v_p_2692_, v_borrow_boxed_2700_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2702_, lean_object* v_decl_2703_, lean_object* v_type_2704_, lean_object* v_value_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_fvarId_2708_; lean_object* v_binderName_2709_; lean_object* v_type_2710_; lean_object* v_value_2711_; size_t v___x_2727_; size_t v___x_2728_; uint8_t v___x_2729_; 
v_fvarId_2708_ = lean_ctor_get(v_decl_2703_, 0);
v_binderName_2709_ = lean_ctor_get(v_decl_2703_, 1);
v_type_2710_ = lean_ctor_get(v_decl_2703_, 2);
v_value_2711_ = lean_ctor_get(v_decl_2703_, 3);
v___x_2727_ = lean_ptr_addr(v_type_2704_);
v___x_2728_ = lean_ptr_addr(v_type_2710_);
v___x_2729_ = lean_usize_dec_eq(v___x_2727_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_inc(v_binderName_2709_);
lean_inc(v_fvarId_2708_);
lean_dec_ref(v_decl_2703_);
goto v___jp_2712_;
}
else
{
size_t v___x_2730_; size_t v___x_2731_; uint8_t v___x_2732_; 
v___x_2730_ = lean_ptr_addr(v_value_2705_);
v___x_2731_ = lean_ptr_addr(v_value_2711_);
v___x_2732_ = lean_usize_dec_eq(v___x_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_inc(v_binderName_2709_);
lean_inc(v_fvarId_2708_);
lean_dec_ref(v_decl_2703_);
goto v___jp_2712_;
}
else
{
lean_object* v___x_2733_; 
lean_dec(v_value_2705_);
lean_dec_ref(v_type_2704_);
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_decl_2703_);
return v___x_2733_;
}
}
v___jp_2712_:
{
lean_object* v_decl_2713_; lean_object* v___x_2714_; lean_object* v_lctx_2715_; lean_object* v_nextIdx_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2726_; 
v_decl_2713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2713_, 0, v_fvarId_2708_);
lean_ctor_set(v_decl_2713_, 1, v_binderName_2709_);
lean_ctor_set(v_decl_2713_, 2, v_type_2704_);
lean_ctor_set(v_decl_2713_, 3, v_value_2705_);
v___x_2714_ = lean_st_ref_take(v_a_2706_);
v_lctx_2715_ = lean_ctor_get(v___x_2714_, 0);
v_nextIdx_2716_ = lean_ctor_get(v___x_2714_, 1);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2718_ = v___x_2714_;
v_isShared_2719_ = v_isSharedCheck_2726_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_nextIdx_2716_);
lean_inc(v_lctx_2715_);
lean_dec(v___x_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2726_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_inc_ref(v_decl_2713_);
v___x_2720_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2702_, v_lctx_2715_, v_decl_2713_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_nextIdx_2716_);
v___x_2722_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_st_ref_put(v_a_2706_, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_decl_2713_);
return v___x_2724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2734_, lean_object* v_decl_2735_, lean_object* v_type_2736_, lean_object* v_value_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
uint8_t v_pu_boxed_2740_; lean_object* v_res_2741_; 
v_pu_boxed_2740_ = lean_unbox(v_pu_2734_);
v_res_2741_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2740_, v_decl_2735_, v_type_2736_, v_value_2737_, v_a_2738_);
lean_dec(v_a_2738_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2742_, lean_object* v_decl_2743_, lean_object* v_type_2744_, lean_object* v_value_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2742_, v_decl_2743_, v_type_2744_, v_value_2745_, v_a_2747_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2752_, lean_object* v_decl_2753_, lean_object* v_type_2754_, lean_object* v_value_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
uint8_t v_pu_boxed_2761_; lean_object* v_res_2762_; 
v_pu_boxed_2761_ = lean_unbox(v_pu_2752_);
v_res_2762_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2761_, v_decl_2753_, v_type_2754_, v_value_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2763_, lean_object* v_decl_2764_, lean_object* v_value_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_type_2768_; lean_object* v___x_2769_; 
v_type_2768_ = lean_ctor_get(v_decl_2764_, 2);
lean_inc_ref(v_type_2768_);
v___x_2769_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2763_, v_decl_2764_, v_type_2768_, v_value_2765_, v_a_2766_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2770_, lean_object* v_decl_2771_, lean_object* v_value_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
uint8_t v_pu_boxed_2775_; lean_object* v_res_2776_; 
v_pu_boxed_2775_ = lean_unbox(v_pu_2770_);
v_res_2776_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2775_, v_decl_2771_, v_value_2772_, v_a_2773_);
lean_dec(v_a_2773_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2777_, lean_object* v_decl_2778_, lean_object* v_value_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2777_, v_decl_2778_, v_value_2779_, v_a_2781_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2786_, lean_object* v_decl_2787_, lean_object* v_value_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
uint8_t v_pu_boxed_2794_; lean_object* v_res_2795_; 
v_pu_boxed_2794_ = lean_unbox(v_pu_2786_);
v_res_2795_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2794_, v_decl_2787_, v_value_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2796_, lean_object* v_decl_2797_, lean_object* v_type_2798_, lean_object* v_params_2799_, lean_object* v_value_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_fvarId_2803_; lean_object* v_binderName_2804_; lean_object* v_params_2805_; lean_object* v_type_2806_; lean_object* v_value_2807_; size_t v___x_2823_; size_t v___x_2824_; uint8_t v___x_2825_; 
v_fvarId_2803_ = lean_ctor_get(v_decl_2797_, 0);
v_binderName_2804_ = lean_ctor_get(v_decl_2797_, 1);
v_params_2805_ = lean_ctor_get(v_decl_2797_, 2);
v_type_2806_ = lean_ctor_get(v_decl_2797_, 3);
v_value_2807_ = lean_ctor_get(v_decl_2797_, 4);
v___x_2823_ = lean_ptr_addr(v_type_2798_);
v___x_2824_ = lean_ptr_addr(v_type_2806_);
v___x_2825_ = lean_usize_dec_eq(v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_inc(v_binderName_2804_);
lean_inc(v_fvarId_2803_);
lean_dec_ref(v_decl_2797_);
goto v___jp_2808_;
}
else
{
size_t v___x_2826_; size_t v___x_2827_; uint8_t v___x_2828_; 
v___x_2826_ = lean_ptr_addr(v_params_2799_);
v___x_2827_ = lean_ptr_addr(v_params_2805_);
v___x_2828_ = lean_usize_dec_eq(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_inc(v_binderName_2804_);
lean_inc(v_fvarId_2803_);
lean_dec_ref(v_decl_2797_);
goto v___jp_2808_;
}
else
{
size_t v___x_2829_; size_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = lean_ptr_addr(v_value_2800_);
v___x_2830_ = lean_ptr_addr(v_value_2807_);
v___x_2831_ = lean_usize_dec_eq(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_inc(v_binderName_2804_);
lean_inc(v_fvarId_2803_);
lean_dec_ref(v_decl_2797_);
goto v___jp_2808_;
}
else
{
lean_object* v___x_2832_; 
lean_dec_ref(v_value_2800_);
lean_dec_ref(v_params_2799_);
lean_dec_ref(v_type_2798_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_decl_2797_);
return v___x_2832_;
}
}
}
v___jp_2808_:
{
lean_object* v_decl_2809_; lean_object* v___x_2810_; lean_object* v_lctx_2811_; lean_object* v_nextIdx_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2822_; 
v_decl_2809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2809_, 0, v_fvarId_2803_);
lean_ctor_set(v_decl_2809_, 1, v_binderName_2804_);
lean_ctor_set(v_decl_2809_, 2, v_params_2799_);
lean_ctor_set(v_decl_2809_, 3, v_type_2798_);
lean_ctor_set(v_decl_2809_, 4, v_value_2800_);
v___x_2810_ = lean_st_ref_take(v_a_2801_);
v_lctx_2811_ = lean_ctor_get(v___x_2810_, 0);
v_nextIdx_2812_ = lean_ctor_get(v___x_2810_, 1);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2814_ = v___x_2810_;
v_isShared_2815_ = v_isSharedCheck_2822_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_nextIdx_2812_);
lean_inc(v_lctx_2811_);
lean_dec(v___x_2810_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2822_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
lean_inc_ref(v_decl_2809_);
v___x_2816_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2796_, v_lctx_2811_, v_decl_2809_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2816_);
v___x_2818_ = v___x_2814_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_nextIdx_2812_);
v___x_2818_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_st_ref_put(v_a_2801_, v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v_decl_2809_);
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2833_, lean_object* v_decl_2834_, lean_object* v_type_2835_, lean_object* v_params_2836_, lean_object* v_value_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
uint8_t v_pu_boxed_2840_; lean_object* v_res_2841_; 
v_pu_boxed_2840_ = lean_unbox(v_pu_2833_);
v_res_2841_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2840_, v_decl_2834_, v_type_2835_, v_params_2836_, v_value_2837_, v_a_2838_);
lean_dec(v_a_2838_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2842_, lean_object* v_decl_2843_, lean_object* v_type_2844_, lean_object* v_params_2845_, lean_object* v_value_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2842_, v_decl_2843_, v_type_2844_, v_params_2845_, v_value_2846_, v_a_2848_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2853_, lean_object* v_decl_2854_, lean_object* v_type_2855_, lean_object* v_params_2856_, lean_object* v_value_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
uint8_t v_pu_boxed_2863_; lean_object* v_res_2864_; 
v_pu_boxed_2863_ = lean_unbox(v_pu_2853_);
v_res_2864_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2863_, v_decl_2854_, v_type_2855_, v_params_2856_, v_value_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2865_, lean_object* v_decl_2866_, lean_object* v_type_2867_, lean_object* v_value_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_params_2871_; lean_object* v___x_2872_; 
v_params_2871_ = lean_ctor_get(v_decl_2866_, 2);
lean_inc_ref(v_params_2871_);
v___x_2872_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2865_, v_decl_2866_, v_type_2867_, v_params_2871_, v_value_2868_, v_a_2869_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2873_, lean_object* v_decl_2874_, lean_object* v_type_2875_, lean_object* v_value_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
uint8_t v_pu_boxed_2879_; lean_object* v_res_2880_; 
v_pu_boxed_2879_ = lean_unbox(v_pu_2873_);
v_res_2880_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2879_, v_decl_2874_, v_type_2875_, v_value_2876_, v_a_2877_);
lean_dec(v_a_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2881_, lean_object* v_decl_2882_, lean_object* v_type_2883_, lean_object* v_value_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_params_2890_; lean_object* v___x_2891_; 
v_params_2890_ = lean_ctor_get(v_decl_2882_, 2);
lean_inc_ref(v_params_2890_);
v___x_2891_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2881_, v_decl_2882_, v_type_2883_, v_params_2890_, v_value_2884_, v_a_2886_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2892_, lean_object* v_decl_2893_, lean_object* v_type_2894_, lean_object* v_value_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
uint8_t v_pu_boxed_2901_; lean_object* v_res_2902_; 
v_pu_boxed_2901_ = lean_unbox(v_pu_2892_);
v_res_2902_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2901_, v_decl_2893_, v_type_2894_, v_value_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2903_, lean_object* v_decl_2904_, lean_object* v_value_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_params_2908_; lean_object* v_type_2909_; lean_object* v___x_2910_; 
v_params_2908_ = lean_ctor_get(v_decl_2904_, 2);
lean_inc_ref(v_params_2908_);
v_type_2909_ = lean_ctor_get(v_decl_2904_, 3);
lean_inc_ref(v_type_2909_);
v___x_2910_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2903_, v_decl_2904_, v_type_2909_, v_params_2908_, v_value_2905_, v_a_2906_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2911_, lean_object* v_decl_2912_, lean_object* v_value_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
uint8_t v_pu_boxed_2916_; lean_object* v_res_2917_; 
v_pu_boxed_2916_ = lean_unbox(v_pu_2911_);
v_res_2917_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2916_, v_decl_2912_, v_value_2913_, v_a_2914_);
lean_dec(v_a_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2918_, lean_object* v_decl_2919_, lean_object* v_value_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_params_2926_; lean_object* v_type_2927_; lean_object* v___x_2928_; 
v_params_2926_ = lean_ctor_get(v_decl_2919_, 2);
lean_inc_ref(v_params_2926_);
v_type_2927_ = lean_ctor_get(v_decl_2919_, 3);
lean_inc_ref(v_type_2927_);
v___x_2928_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2918_, v_decl_2919_, v_type_2927_, v_params_2926_, v_value_2920_, v_a_2922_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2929_, lean_object* v_decl_2930_, lean_object* v_value_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
uint8_t v_pu_boxed_2937_; lean_object* v_res_2938_; 
v_pu_boxed_2937_ = lean_unbox(v_pu_2929_);
v_res_2938_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2937_, v_decl_2930_, v_value_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2939_, lean_object* v_p_2940_, lean_object* v_inst_2941_, lean_object* v_____do__lift_2942_){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_box(v_pu_2939_);
v___x_2944_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2944_, 0, v___x_2943_);
lean_closure_set(v___x_2944_, 1, v_p_2940_);
lean_closure_set(v___x_2944_, 2, v_____do__lift_2942_);
v___x_2945_ = lean_apply_2(v_inst_2941_, lean_box(0), v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2946_, lean_object* v_p_2947_, lean_object* v_inst_2948_, lean_object* v_____do__lift_2949_){
_start:
{
uint8_t v_pu_boxed_2950_; lean_object* v_res_2951_; 
v_pu_boxed_2950_ = lean_unbox(v_pu_2946_);
v_res_2951_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2950_, v_p_2947_, v_inst_2948_, v_____do__lift_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2952_, uint8_t v_t_2953_, lean_object* v_type_2954_, lean_object* v_toPure_2955_, lean_object* v_____do__lift_2956_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2952_, v_____do__lift_2956_, v_t_2953_, v_type_2954_);
v___x_2958_ = lean_apply_2(v_toPure_2955_, lean_box(0), v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2959_, lean_object* v_t_2960_, lean_object* v_type_2961_, lean_object* v_toPure_2962_, lean_object* v_____do__lift_2963_){
_start:
{
uint8_t v_pu_boxed_2964_; uint8_t v_t_boxed_2965_; lean_object* v_res_2966_; 
v_pu_boxed_2964_ = lean_unbox(v_pu_2959_);
v_t_boxed_2965_ = lean_unbox(v_t_2960_);
v_res_2966_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2964_, v_t_boxed_2965_, v_type_2961_, v_toPure_2962_, v_____do__lift_2963_);
lean_dec_ref(v_____do__lift_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2967_, uint8_t v_t_2968_, lean_object* v_inst_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_p_2972_){
_start:
{
lean_object* v_toApplicative_2973_; lean_object* v_toBind_2974_; lean_object* v_type_2975_; lean_object* v_toPure_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_toApplicative_2973_ = lean_ctor_get(v_inst_2970_, 0);
lean_inc_ref(v_toApplicative_2973_);
v_toBind_2974_ = lean_ctor_get(v_inst_2970_, 1);
lean_inc_n(v_toBind_2974_, 2);
lean_dec_ref(v_inst_2970_);
v_type_2975_ = lean_ctor_get(v_p_2972_, 2);
lean_inc_ref(v_type_2975_);
v_toPure_2976_ = lean_ctor_get(v_toApplicative_2973_, 1);
lean_inc(v_toPure_2976_);
lean_dec_ref(v_toApplicative_2973_);
v___x_2977_ = lean_box(v_pu_2967_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2978_, 0, v___x_2977_);
lean_closure_set(v___f_2978_, 1, v_p_2972_);
lean_closure_set(v___f_2978_, 2, v_inst_2969_);
v___x_2979_ = lean_box(v_pu_2967_);
v___x_2980_ = lean_box(v_t_2968_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2981_, 0, v___x_2979_);
lean_closure_set(v___f_2981_, 1, v___x_2980_);
lean_closure_set(v___f_2981_, 2, v_type_2975_);
lean_closure_set(v___f_2981_, 3, v_toPure_2976_);
v___x_2982_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v_inst_2971_, v___f_2981_);
v___x_2983_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2982_, v___f_2978_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2984_, lean_object* v_t_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_p_2989_){
_start:
{
uint8_t v_pu_boxed_2990_; uint8_t v_t_boxed_2991_; lean_object* v_res_2992_; 
v_pu_boxed_2990_ = lean_unbox(v_pu_2984_);
v_t_boxed_2991_ = lean_unbox(v_t_2985_);
v_res_2992_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_2990_, v_t_boxed_2991_, v_inst_2986_, v_inst_2987_, v_inst_2988_, v_p_2989_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_2993_, uint8_t v_pu_2994_, uint8_t v_t_2995_, lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_p_2999_){
_start:
{
lean_object* v_toApplicative_3000_; lean_object* v_toBind_3001_; lean_object* v_type_3002_; lean_object* v_toPure_3003_; lean_object* v___x_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_toApplicative_3000_ = lean_ctor_get(v_inst_2997_, 0);
lean_inc_ref(v_toApplicative_3000_);
v_toBind_3001_ = lean_ctor_get(v_inst_2997_, 1);
lean_inc_n(v_toBind_3001_, 2);
lean_dec_ref(v_inst_2997_);
v_type_3002_ = lean_ctor_get(v_p_2999_, 2);
lean_inc_ref(v_type_3002_);
v_toPure_3003_ = lean_ctor_get(v_toApplicative_3000_, 1);
lean_inc(v_toPure_3003_);
lean_dec_ref(v_toApplicative_3000_);
v___x_3004_ = lean_box(v_pu_2994_);
v___f_3005_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3005_, 0, v___x_3004_);
lean_closure_set(v___f_3005_, 1, v_p_2999_);
lean_closure_set(v___f_3005_, 2, v_inst_2996_);
v___x_3006_ = lean_box(v_pu_2994_);
v___x_3007_ = lean_box(v_t_2995_);
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3008_, 0, v___x_3006_);
lean_closure_set(v___f_3008_, 1, v___x_3007_);
lean_closure_set(v___f_3008_, 2, v_type_3002_);
lean_closure_set(v___f_3008_, 3, v_toPure_3003_);
v___x_3009_ = lean_apply_4(v_toBind_3001_, lean_box(0), lean_box(0), v_inst_2998_, v___f_3008_);
v___x_3010_ = lean_apply_4(v_toBind_3001_, lean_box(0), lean_box(0), v___x_3009_, v___f_3005_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3011_, lean_object* v_pu_3012_, lean_object* v_t_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_p_3017_){
_start:
{
uint8_t v_pu_boxed_3018_; uint8_t v_t_boxed_3019_; lean_object* v_res_3020_; 
v_pu_boxed_3018_ = lean_unbox(v_pu_3012_);
v_t_boxed_3019_ = lean_unbox(v_t_3013_);
v_res_3020_ = l_Lean_Compiler_LCNF_normParam(v_m_3011_, v_pu_boxed_3018_, v_t_boxed_3019_, v_inst_3014_, v_inst_3015_, v_inst_3016_, v_p_3017_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3021_, uint8_t v_t_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_ps_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3027_ = lean_box(v_pu_3021_);
v___x_3028_ = lean_box(v_t_3022_);
lean_inc_ref(v_inst_3024_);
v___x_3029_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3029_, 0, lean_box(0));
lean_closure_set(v___x_3029_, 1, v___x_3027_);
lean_closure_set(v___x_3029_, 2, v___x_3028_);
lean_closure_set(v___x_3029_, 3, v_inst_3023_);
lean_closure_set(v___x_3029_, 4, v_inst_3024_);
lean_closure_set(v___x_3029_, 5, v_inst_3025_);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3024_, v___x_3029_, v___x_3030_, v_ps_3026_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3032_, lean_object* v_t_3033_, lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_ps_3037_){
_start:
{
uint8_t v_pu_boxed_3038_; uint8_t v_t_boxed_3039_; lean_object* v_res_3040_; 
v_pu_boxed_3038_ = lean_unbox(v_pu_3032_);
v_t_boxed_3039_ = lean_unbox(v_t_3033_);
v_res_3040_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3038_, v_t_boxed_3039_, v_inst_3034_, v_inst_3035_, v_inst_3036_, v_ps_3037_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3041_, uint8_t v_pu_3042_, uint8_t v_t_3043_, lean_object* v_inst_3044_, lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_ps_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3042_, v_t_3043_, v_inst_3044_, v_inst_3045_, v_inst_3046_, v_ps_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3049_, lean_object* v_pu_3050_, lean_object* v_t_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_ps_3055_){
_start:
{
uint8_t v_pu_boxed_3056_; uint8_t v_t_boxed_3057_; lean_object* v_res_3058_; 
v_pu_boxed_3056_ = lean_unbox(v_pu_3050_);
v_t_boxed_3057_ = lean_unbox(v_t_3051_);
v_res_3058_ = l_Lean_Compiler_LCNF_normParams(v_m_3049_, v_pu_boxed_3056_, v_t_boxed_3057_, v_inst_3052_, v_inst_3053_, v_inst_3054_, v_ps_3055_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3059_, lean_object* v_decl_3060_, lean_object* v_____do__lift_3061_, lean_object* v_inst_3062_, lean_object* v_____do__lift_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_box(v_pu_3059_);
v___x_3065_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3065_, 0, v___x_3064_);
lean_closure_set(v___x_3065_, 1, v_decl_3060_);
lean_closure_set(v___x_3065_, 2, v_____do__lift_3061_);
lean_closure_set(v___x_3065_, 3, v_____do__lift_3063_);
v___x_3066_ = lean_apply_2(v_inst_3062_, lean_box(0), v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3067_, lean_object* v_decl_3068_, lean_object* v_____do__lift_3069_, lean_object* v_inst_3070_, lean_object* v_____do__lift_3071_){
_start:
{
uint8_t v_pu_boxed_3072_; lean_object* v_res_3073_; 
v_pu_boxed_3072_ = lean_unbox(v_pu_3067_);
v_res_3073_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3072_, v_decl_3068_, v_____do__lift_3069_, v_inst_3070_, v_____do__lift_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3074_, lean_object* v_value_3075_, uint8_t v_t_3076_, lean_object* v_toPure_3077_, lean_object* v_____do__lift_3078_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3074_, v_____do__lift_3078_, v_value_3075_, v_t_3076_);
v___x_3080_ = lean_apply_2(v_toPure_3077_, lean_box(0), v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3081_, lean_object* v_value_3082_, lean_object* v_t_3083_, lean_object* v_toPure_3084_, lean_object* v_____do__lift_3085_){
_start:
{
uint8_t v_pu_boxed_3086_; uint8_t v_t_boxed_3087_; lean_object* v_res_3088_; 
v_pu_boxed_3086_ = lean_unbox(v_pu_3081_);
v_t_boxed_3087_ = lean_unbox(v_t_3083_);
v_res_3088_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3086_, v_value_3082_, v_t_boxed_3087_, v_toPure_3084_, v_____do__lift_3085_);
lean_dec_ref(v_____do__lift_3085_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3089_, lean_object* v_decl_3090_, lean_object* v_inst_3091_, lean_object* v_value_3092_, uint8_t v_t_3093_, lean_object* v_toPure_3094_, lean_object* v_toBind_3095_, lean_object* v_inst_3096_, lean_object* v_____do__lift_3097_){
_start:
{
lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3098_ = lean_box(v_pu_3089_);
v___f_3099_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3099_, 0, v___x_3098_);
lean_closure_set(v___f_3099_, 1, v_decl_3090_);
lean_closure_set(v___f_3099_, 2, v_____do__lift_3097_);
lean_closure_set(v___f_3099_, 3, v_inst_3091_);
v___x_3100_ = lean_box(v_pu_3089_);
v___x_3101_ = lean_box(v_t_3093_);
v___f_3102_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3102_, 0, v___x_3100_);
lean_closure_set(v___f_3102_, 1, v_value_3092_);
lean_closure_set(v___f_3102_, 2, v___x_3101_);
lean_closure_set(v___f_3102_, 3, v_toPure_3094_);
lean_inc(v_toBind_3095_);
v___x_3103_ = lean_apply_4(v_toBind_3095_, lean_box(0), lean_box(0), v_inst_3096_, v___f_3102_);
v___x_3104_ = lean_apply_4(v_toBind_3095_, lean_box(0), lean_box(0), v___x_3103_, v___f_3099_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3105_, lean_object* v_decl_3106_, lean_object* v_inst_3107_, lean_object* v_value_3108_, lean_object* v_t_3109_, lean_object* v_toPure_3110_, lean_object* v_toBind_3111_, lean_object* v_inst_3112_, lean_object* v_____do__lift_3113_){
_start:
{
uint8_t v_pu_boxed_3114_; uint8_t v_t_boxed_3115_; lean_object* v_res_3116_; 
v_pu_boxed_3114_ = lean_unbox(v_pu_3105_);
v_t_boxed_3115_ = lean_unbox(v_t_3109_);
v_res_3116_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3114_, v_decl_3106_, v_inst_3107_, v_value_3108_, v_t_boxed_3115_, v_toPure_3110_, v_toBind_3111_, v_inst_3112_, v_____do__lift_3113_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3117_, uint8_t v_t_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_decl_3122_){
_start:
{
lean_object* v_toApplicative_3123_; lean_object* v_toBind_3124_; lean_object* v_type_3125_; lean_object* v_value_3126_; lean_object* v_toPure_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v_toApplicative_3123_ = lean_ctor_get(v_inst_3120_, 0);
lean_inc_ref(v_toApplicative_3123_);
v_toBind_3124_ = lean_ctor_get(v_inst_3120_, 1);
lean_inc_n(v_toBind_3124_, 3);
lean_dec_ref(v_inst_3120_);
v_type_3125_ = lean_ctor_get(v_decl_3122_, 2);
lean_inc_ref(v_type_3125_);
v_value_3126_ = lean_ctor_get(v_decl_3122_, 3);
lean_inc(v_value_3126_);
v_toPure_3127_ = lean_ctor_get(v_toApplicative_3123_, 1);
lean_inc_n(v_toPure_3127_, 2);
lean_dec_ref(v_toApplicative_3123_);
v___x_3128_ = lean_box(v_pu_3117_);
v___x_3129_ = lean_box(v_t_3118_);
lean_inc(v_inst_3121_);
v___f_3130_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3130_, 0, v___x_3128_);
lean_closure_set(v___f_3130_, 1, v_decl_3122_);
lean_closure_set(v___f_3130_, 2, v_inst_3119_);
lean_closure_set(v___f_3130_, 3, v_value_3126_);
lean_closure_set(v___f_3130_, 4, v___x_3129_);
lean_closure_set(v___f_3130_, 5, v_toPure_3127_);
lean_closure_set(v___f_3130_, 6, v_toBind_3124_);
lean_closure_set(v___f_3130_, 7, v_inst_3121_);
v___x_3131_ = lean_box(v_pu_3117_);
v___x_3132_ = lean_box(v_t_3118_);
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3133_, 0, v___x_3131_);
lean_closure_set(v___f_3133_, 1, v___x_3132_);
lean_closure_set(v___f_3133_, 2, v_type_3125_);
lean_closure_set(v___f_3133_, 3, v_toPure_3127_);
v___x_3134_ = lean_apply_4(v_toBind_3124_, lean_box(0), lean_box(0), v_inst_3121_, v___f_3133_);
v___x_3135_ = lean_apply_4(v_toBind_3124_, lean_box(0), lean_box(0), v___x_3134_, v___f_3130_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3136_, lean_object* v_t_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_decl_3141_){
_start:
{
uint8_t v_pu_boxed_3142_; uint8_t v_t_boxed_3143_; lean_object* v_res_3144_; 
v_pu_boxed_3142_ = lean_unbox(v_pu_3136_);
v_t_boxed_3143_ = lean_unbox(v_t_3137_);
v_res_3144_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3142_, v_t_boxed_3143_, v_inst_3138_, v_inst_3139_, v_inst_3140_, v_decl_3141_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3145_, uint8_t v_pu_3146_, uint8_t v_t_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_decl_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3146_, v_t_3147_, v_inst_3148_, v_inst_3149_, v_inst_3150_, v_decl_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3153_, lean_object* v_pu_3154_, lean_object* v_t_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_decl_3159_){
_start:
{
uint8_t v_pu_boxed_3160_; uint8_t v_t_boxed_3161_; lean_object* v_res_3162_; 
v_pu_boxed_3160_ = lean_unbox(v_pu_3154_);
v_t_boxed_3161_ = lean_unbox(v_t_3155_);
v_res_3162_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3153_, v_pu_boxed_3160_, v_t_boxed_3161_, v_inst_3156_, v_inst_3157_, v_inst_3158_, v_decl_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg(){
_start:
{
lean_object* v___x_3164_; lean_object* v_toApplicative_3165_; lean_object* v_toFunctor_3166_; lean_object* v_toSeq_3167_; lean_object* v_toSeqLeft_3168_; lean_object* v_toSeqRight_3169_; lean_object* v___f_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___f_3173_; lean_object* v___x_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_toApplicative_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3209_; 
v___x_3164_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3165_ = lean_ctor_get(v___x_3164_, 0);
v_toFunctor_3166_ = lean_ctor_get(v_toApplicative_3165_, 0);
v_toSeq_3167_ = lean_ctor_get(v_toApplicative_3165_, 2);
v_toSeqLeft_3168_ = lean_ctor_get(v_toApplicative_3165_, 3);
v_toSeqRight_3169_ = lean_ctor_get(v_toApplicative_3165_, 4);
v___f_3170_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3171_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3166_, 2);
v___f_3172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3172_, 0, v_toFunctor_3166_);
v___f_3173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3173_, 0, v_toFunctor_3166_);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___f_3172_);
lean_ctor_set(v___x_3174_, 1, v___f_3173_);
lean_inc(v_toSeqRight_3169_);
v___f_3175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3175_, 0, v_toSeqRight_3169_);
lean_inc(v_toSeqLeft_3168_);
v___f_3176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3176_, 0, v_toSeqLeft_3168_);
lean_inc(v_toSeq_3167_);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toSeq_3167_);
v___x_3178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3174_);
lean_ctor_set(v___x_3178_, 1, v___f_3170_);
lean_ctor_set(v___x_3178_, 2, v___f_3177_);
lean_ctor_set(v___x_3178_, 3, v___f_3176_);
lean_ctor_set(v___x_3178_, 4, v___f_3175_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___f_3171_);
v___x_3180_ = l_StateRefT_x27_instMonad___redArg(v___x_3179_);
v_toApplicative_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3180_, 1);
lean_dec(v_unused_3210_);
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3209_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_toApplicative_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3209_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_toFunctor_3185_; lean_object* v_toSeq_3186_; lean_object* v_toSeqLeft_3187_; lean_object* v_toSeqRight_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3207_; 
v_toFunctor_3185_ = lean_ctor_get(v_toApplicative_3181_, 0);
v_toSeq_3186_ = lean_ctor_get(v_toApplicative_3181_, 2);
v_toSeqLeft_3187_ = lean_ctor_get(v_toApplicative_3181_, 3);
v_toSeqRight_3188_ = lean_ctor_get(v_toApplicative_3181_, 4);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_toApplicative_3181_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v_toApplicative_3181_, 1);
lean_dec(v_unused_3208_);
v___x_3190_ = v_toApplicative_3181_;
v_isShared_3191_ = v_isSharedCheck_3207_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_toSeqRight_3188_);
lean_inc(v_toSeqLeft_3187_);
lean_inc(v_toSeq_3186_);
lean_inc(v_toFunctor_3185_);
lean_dec(v_toApplicative_3181_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3207_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___f_3192_; lean_object* v___f_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___x_3196_; lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___x_3201_; 
v___f_3192_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3193_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3185_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toFunctor_3185_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toFunctor_3185_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___f_3194_);
lean_ctor_set(v___x_3196_, 1, v___f_3195_);
v___f_3197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3197_, 0, v_toSeqRight_3188_);
v___f_3198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3198_, 0, v_toSeqLeft_3187_);
v___f_3199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3199_, 0, v_toSeq_3186_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 4, v___f_3197_);
lean_ctor_set(v___x_3190_, 3, v___f_3198_);
lean_ctor_set(v___x_3190_, 2, v___f_3199_);
lean_ctor_set(v___x_3190_, 1, v___f_3192_);
lean_ctor_set(v___x_3190_, 0, v___x_3196_);
v___x_3201_ = v___x_3190_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___f_3192_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v___f_3199_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v___f_3198_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v___f_3197_);
v___x_3201_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 1, v___f_3193_);
lean_ctor_set(v___x_3183_, 0, v___x_3201_);
v___x_3203_ = v___x_3183_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___f_3193_);
v___x_3203_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3204_, 0, lean_box(0));
lean_closure_set(v___x_3204_, 1, lean_box(0));
lean_closure_set(v___x_3204_, 2, v___x_3203_);
return v___x_3204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object* v___dummy_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v_res_3212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0(void){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3214_, uint8_t v_t_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0, &l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3217_, lean_object* v_t_3218_){
_start:
{
uint8_t v_pu_boxed_3219_; uint8_t v_t_boxed_3220_; lean_object* v_res_3221_; 
v_pu_boxed_3219_ = lean_unbox(v_pu_3217_);
v_t_boxed_3220_ = lean_unbox(v_t_3218_);
v_res_3221_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3219_, v_t_boxed_3220_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3222_, lean_object* v_inst_3223_, lean_object* v_result_3224_, lean_object* v_x_3225_){
_start:
{
if (lean_obj_tag(v_result_3224_) == 0)
{
lean_object* v_fvarId_3226_; lean_object* v___x_3227_; 
lean_dec(v_inst_3223_);
v_fvarId_3226_ = lean_ctor_get(v_result_3224_, 0);
lean_inc(v_fvarId_3226_);
lean_dec_ref_known(v_result_3224_, 1);
v___x_3227_ = lean_apply_1(v_x_3225_, v_fvarId_3226_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec(v_x_3225_);
v___x_3228_ = lean_box(v_pu_3222_);
v___x_3229_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3229_, 0, v___x_3228_);
v___x_3230_ = lean_apply_2(v_inst_3223_, lean_box(0), v___x_3229_);
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3231_, lean_object* v_inst_3232_, lean_object* v_result_3233_, lean_object* v_x_3234_){
_start:
{
uint8_t v_pu_boxed_3235_; lean_object* v_res_3236_; 
v_pu_boxed_3235_ = lean_unbox(v_pu_3231_);
v_res_3236_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3235_, v_inst_3232_, v_result_3233_, v_x_3234_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3237_, uint8_t v_pu_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_result_3241_, lean_object* v_x_3242_){
_start:
{
if (lean_obj_tag(v_result_3241_) == 0)
{
lean_object* v_fvarId_3243_; lean_object* v___x_3244_; 
lean_dec(v_inst_3239_);
v_fvarId_3243_ = lean_ctor_get(v_result_3241_, 0);
lean_inc(v_fvarId_3243_);
lean_dec_ref_known(v_result_3241_, 1);
v___x_3244_ = lean_apply_1(v_x_3242_, v_fvarId_3243_);
return v___x_3244_;
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec(v_x_3242_);
v___x_3245_ = lean_box(v_pu_3238_);
v___x_3246_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3246_, 0, v___x_3245_);
v___x_3247_ = lean_apply_2(v_inst_3239_, lean_box(0), v___x_3246_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3248_, lean_object* v_pu_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_result_3252_, lean_object* v_x_3253_){
_start:
{
uint8_t v_pu_boxed_3254_; lean_object* v_res_3255_; 
v_pu_boxed_3254_ = lean_unbox(v_pu_3249_);
v_res_3255_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3248_, v_pu_boxed_3254_, v_inst_3250_, v_inst_3251_, v_result_3252_, v_x_3253_);
lean_dec_ref(v_inst_3251_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3256_, uint8_t v_t_3257_, lean_object* v_args_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3256_, v___y_3259_, v_args_3258_, v_t_3257_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3263_, lean_object* v_t_3264_, lean_object* v_args_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_pu_boxed_3268_; uint8_t v_t_boxed_3269_; lean_object* v_res_3270_; 
v_pu_boxed_3268_ = lean_unbox(v_pu_3263_);
v_t_boxed_3269_ = lean_unbox(v_t_3264_);
v_res_3270_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3268_, v_t_boxed_3269_, v_args_3265_, v___y_3266_);
lean_dec_ref(v___y_3266_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3271_, uint8_t v_t_3272_, lean_object* v_i_3273_, lean_object* v_as_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = lean_array_get_size(v_as_3274_);
v___x_3279_ = lean_nat_dec_lt(v_i_3273_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
lean_dec(v_i_3273_);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_as_3274_);
return v___x_3280_;
}
else
{
lean_object* v_a_3281_; lean_object* v_type_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_a_3281_ = lean_array_fget_borrowed(v_as_3274_, v_i_3273_);
v_type_3282_ = lean_ctor_get(v_a_3281_, 2);
lean_inc_ref(v_type_3282_);
v___x_3283_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3271_, v___y_3275_, v_t_3272_, v_type_3282_);
lean_inc(v_a_3281_);
v___x_3284_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3271_, v_a_3281_, v___x_3283_, v___y_3276_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; size_t v___x_3286_; size_t v___x_3287_; uint8_t v___x_3288_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = lean_ptr_addr(v_a_3281_);
v___x_3287_ = lean_ptr_addr(v_a_3285_);
v___x_3288_ = lean_usize_dec_eq(v___x_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = lean_unsigned_to_nat(1u);
v___x_3290_ = lean_nat_add(v_i_3273_, v___x_3289_);
v___x_3291_ = lean_array_fset(v_as_3274_, v_i_3273_, v_a_3285_);
lean_dec(v_i_3273_);
v_i_3273_ = v___x_3290_;
v_as_3274_ = v___x_3291_;
goto _start;
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v_a_3285_);
v___x_3293_ = lean_unsigned_to_nat(1u);
v___x_3294_ = lean_nat_add(v_i_3273_, v___x_3293_);
lean_dec(v_i_3273_);
v_i_3273_ = v___x_3294_;
goto _start;
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v_as_3274_);
lean_dec(v_i_3273_);
v_a_3296_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3284_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3284_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3304_, lean_object* v_t_3305_, lean_object* v_i_3306_, lean_object* v_as_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v_pu_boxed_3311_; uint8_t v_t_boxed_3312_; lean_object* v_res_3313_; 
v_pu_boxed_3311_ = lean_unbox(v_pu_3304_);
v_t_boxed_3312_ = lean_unbox(v_t_3305_);
v_res_3313_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3311_, v_t_boxed_3312_, v_i_3306_, v_as_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3314_, uint8_t v_t_3315_, lean_object* v_ps_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3314_, v_t_3315_, v___x_3323_, v_ps_3316_, v___y_3317_, v___y_3319_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3325_, lean_object* v_t_3326_, lean_object* v_ps_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v_pu_boxed_3334_; uint8_t v_t_boxed_3335_; lean_object* v_res_3336_; 
v_pu_boxed_3334_ = lean_unbox(v_pu_3325_);
v_t_boxed_3335_ = lean_unbox(v_t_3326_);
v_res_3336_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3334_, v_t_boxed_3335_, v_ps_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3337_, uint8_t v_t_3338_, lean_object* v_decl_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_type_3343_; lean_object* v_value_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_type_3343_ = lean_ctor_get(v_decl_3339_, 2);
v_value_3344_ = lean_ctor_get(v_decl_3339_, 3);
lean_inc_ref(v_type_3343_);
v___x_3345_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3337_, v___y_3340_, v_t_3338_, v_type_3343_);
lean_inc(v_value_3344_);
v___x_3346_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3337_, v___y_3340_, v_value_3344_, v_t_3338_);
v___x_3347_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3337_, v_decl_3339_, v___x_3345_, v___x_3346_, v___y_3341_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3348_, lean_object* v_t_3349_, lean_object* v_decl_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
uint8_t v_pu_boxed_3354_; uint8_t v_t_boxed_3355_; lean_object* v_res_3356_; 
v_pu_boxed_3354_ = lean_unbox(v_pu_3348_);
v_t_boxed_3355_ = lean_unbox(v_t_3349_);
v_res_3356_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3354_, v_t_boxed_3355_, v_decl_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3357_, uint8_t v_t_3358_, lean_object* v_i_3359_, lean_object* v_as_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3367_ = lean_array_get_size(v_as_3360_);
v___x_3368_ = lean_nat_dec_lt(v_i_3359_, v___x_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; 
lean_dec(v_i_3359_);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_as_3360_);
return v___x_3369_;
}
else
{
lean_object* v_a_3370_; lean_object* v_a_3372_; 
v_a_3370_ = lean_array_fget_borrowed(v_as_3360_, v_i_3359_);
switch(lean_obj_tag(v_a_3370_))
{
case 0:
{
lean_object* v_params_3383_; lean_object* v_code_3384_; lean_object* v___x_3385_; 
v_params_3383_ = lean_ctor_get(v_a_3370_, 1);
v_code_3384_ = lean_ctor_get(v_a_3370_, 2);
lean_inc_ref(v_params_3383_);
v___x_3385_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3357_, v_t_3358_, v_params_3383_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
lean_inc_ref(v_code_3384_);
v___x_3387_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3357_, v_t_3358_, v_code_3384_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
lean_inc_ref(v_a_3370_);
v___x_3389_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3357_, v_a_3370_, v_a_3386_, v_a_3388_);
v_a_3372_ = v___x_3389_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_a_3386_);
lean_dec_ref(v_as_3360_);
lean_dec(v_i_3359_);
v_a_3390_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3387_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3387_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v_as_3360_);
lean_dec(v_i_3359_);
v_a_3398_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3385_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3385_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
case 1:
{
lean_object* v_code_3406_; lean_object* v___x_3407_; 
v_code_3406_ = lean_ctor_get(v_a_3370_, 1);
lean_inc_ref(v_code_3406_);
v___x_3407_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3357_, v_t_3358_, v_code_3406_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
lean_inc_ref(v_a_3370_);
v___x_3409_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3370_, v_a_3408_);
v_a_3372_ = v___x_3409_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v_as_3360_);
lean_dec(v_i_3359_);
v_a_3410_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3407_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3407_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
default: 
{
lean_object* v_code_3418_; lean_object* v___x_3419_; 
v_code_3418_ = lean_ctor_get(v_a_3370_, 0);
lean_inc_ref(v_code_3418_);
v___x_3419_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3357_, v_t_3358_, v_code_3418_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
lean_inc_ref(v_a_3370_);
v___x_3421_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3370_, v_a_3420_);
v_a_3372_ = v___x_3421_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_as_3360_);
lean_dec(v_i_3359_);
v_a_3422_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3419_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3419_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
v___jp_3371_:
{
size_t v___x_3373_; size_t v___x_3374_; uint8_t v___x_3375_; 
v___x_3373_ = lean_ptr_addr(v_a_3370_);
v___x_3374_ = lean_ptr_addr(v_a_3372_);
v___x_3375_ = lean_usize_dec_eq(v___x_3373_, v___x_3374_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = lean_unsigned_to_nat(1u);
v___x_3377_ = lean_nat_add(v_i_3359_, v___x_3376_);
v___x_3378_ = lean_array_fset(v_as_3360_, v_i_3359_, v_a_3372_);
lean_dec(v_i_3359_);
v_i_3359_ = v___x_3377_;
v_as_3360_ = v___x_3378_;
goto _start;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v_a_3372_);
v___x_3380_ = lean_unsigned_to_nat(1u);
v___x_3381_ = lean_nat_add(v_i_3359_, v___x_3380_);
lean_dec(v_i_3359_);
v_i_3359_ = v___x_3381_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3430_, uint8_t v_t_3431_, lean_object* v_code_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
switch(lean_obj_tag(v_code_3432_))
{
case 0:
{
lean_object* v_decl_3439_; lean_object* v_k_3440_; lean_object* v___x_3441_; 
v_decl_3439_ = lean_ctor_get(v_code_3432_, 0);
v_k_3440_ = lean_ctor_get(v_code_3432_, 1);
lean_inc_ref(v_decl_3439_);
v___x_3441_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3430_, v_t_3431_, v_decl_3439_, v_a_3433_, v_a_3435_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
lean_inc_ref(v_k_3440_);
v___x_3443_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_3440_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3481_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3481_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3481_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
size_t v___x_3448_; size_t v___x_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_ptr_addr(v_k_3440_);
v___x_3449_ = lean_ptr_addr(v_a_3444_);
v___x_3450_ = lean_usize_dec_eq(v___x_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3460_; 
v_isSharedCheck_3460_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; lean_object* v_unused_3462_; 
v_unused_3461_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3462_);
v___x_3452_ = v_code_3432_;
v_isShared_3453_ = v_isSharedCheck_3460_;
goto v_resetjp_3451_;
}
else
{
lean_dec(v_code_3432_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3460_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v_a_3444_);
lean_ctor_set(v___x_3452_, 0, v_a_3442_);
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3442_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_a_3444_);
v___x_3455_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3455_);
v___x_3457_ = v___x_3446_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
size_t v___x_3463_; size_t v___x_3464_; uint8_t v___x_3465_; 
v___x_3463_ = lean_ptr_addr(v_decl_3439_);
v___x_3464_ = lean_ptr_addr(v_a_3442_);
v___x_3465_ = lean_usize_dec_eq(v___x_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; lean_object* v_unused_3477_; 
v_unused_3476_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3477_);
v___x_3467_ = v_code_3432_;
v_isShared_3468_ = v_isSharedCheck_3475_;
goto v_resetjp_3466_;
}
else
{
lean_dec(v_code_3432_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3475_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v_a_3444_);
lean_ctor_set(v___x_3467_, 0, v_a_3442_);
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3442_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_a_3444_);
v___x_3470_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3470_);
v___x_3472_ = v___x_3446_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
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
else
{
lean_object* v___x_3479_; 
lean_dec(v_a_3444_);
lean_dec(v_a_3442_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v_code_3432_);
v___x_3479_ = v___x_3446_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_code_3432_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
else
{
lean_dec(v_a_3442_);
lean_dec_ref_known(v_code_3432_, 2);
return v___x_3443_;
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref_known(v_code_3432_, 2);
v_a_3482_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3441_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3441_);
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
v_decl_3490_ = lean_ctor_get(v_code_3432_, 0);
v_k_3491_ = lean_ctor_get(v_code_3432_, 1);
lean_inc_ref(v_decl_3490_);
v___x_3492_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3430_, v_t_3431_, v_decl_3490_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
lean_inc_ref(v_k_3491_);
v___x_3494_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_3491_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3532_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3532_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3532_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
size_t v___x_3499_; size_t v___x_3500_; uint8_t v___x_3501_; 
v___x_3499_ = lean_ptr_addr(v_k_3491_);
v___x_3500_ = lean_ptr_addr(v_a_3495_);
v___x_3501_ = lean_usize_dec_eq(v___x_3499_, v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3511_; 
v_isSharedCheck_3511_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; lean_object* v_unused_3513_; 
v_unused_3512_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3512_);
v_unused_3513_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3513_);
v___x_3503_ = v_code_3432_;
v_isShared_3504_ = v_isSharedCheck_3511_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v_code_3432_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3511_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v_a_3495_);
lean_ctor_set(v___x_3503_, 0, v_a_3493_);
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3493_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_a_3495_);
v___x_3506_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3508_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3506_);
v___x_3508_ = v___x_3497_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
size_t v___x_3514_; size_t v___x_3515_; uint8_t v___x_3516_; 
v___x_3514_ = lean_ptr_addr(v_decl_3490_);
v___x_3515_ = lean_ptr_addr(v_a_3493_);
v___x_3516_ = lean_usize_dec_eq(v___x_3514_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3526_; 
v_isSharedCheck_3526_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; lean_object* v_unused_3528_; 
v_unused_3527_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3528_);
v___x_3518_ = v_code_3432_;
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
else
{
lean_dec(v_code_3432_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v_a_3495_);
lean_ctor_set(v___x_3518_, 0, v_a_3493_);
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3493_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_a_3495_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3521_);
v___x_3523_ = v___x_3497_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
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
else
{
lean_object* v___x_3530_; 
lean_dec(v_a_3495_);
lean_dec(v_a_3493_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_code_3432_);
v___x_3530_ = v___x_3497_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_code_3432_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
else
{
lean_dec(v_a_3493_);
lean_dec_ref_known(v_code_3432_, 2);
return v___x_3494_;
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref_known(v_code_3432_, 2);
v_a_3533_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3492_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3492_);
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
case 2:
{
lean_object* v_decl_3541_; lean_object* v_k_3542_; lean_object* v___x_3543_; 
v_decl_3541_ = lean_ctor_get(v_code_3432_, 0);
v_k_3542_ = lean_ctor_get(v_code_3432_, 1);
lean_inc_ref(v_decl_3541_);
v___x_3543_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3430_, v_t_3431_, v_decl_3541_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
lean_inc_ref(v_k_3542_);
v___x_3545_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_3542_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3583_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3583_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3583_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
size_t v___x_3550_; size_t v___x_3551_; uint8_t v___x_3552_; 
v___x_3550_ = lean_ptr_addr(v_k_3542_);
v___x_3551_ = lean_ptr_addr(v_a_3546_);
v___x_3552_ = lean_usize_dec_eq(v___x_3550_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3562_; 
v_isSharedCheck_3562_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; lean_object* v_unused_3564_; 
v_unused_3563_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3564_);
v___x_3554_ = v_code_3432_;
v_isShared_3555_ = v_isSharedCheck_3562_;
goto v_resetjp_3553_;
}
else
{
lean_dec(v_code_3432_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3562_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v_a_3546_);
lean_ctor_set(v___x_3554_, 0, v_a_3544_);
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3544_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_a_3546_);
v___x_3557_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v___x_3557_);
v___x_3559_ = v___x_3548_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
size_t v___x_3565_; size_t v___x_3566_; uint8_t v___x_3567_; 
v___x_3565_ = lean_ptr_addr(v_decl_3541_);
v___x_3566_ = lean_ptr_addr(v_a_3544_);
v___x_3567_ = lean_usize_dec_eq(v___x_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
v_isSharedCheck_3577_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; 
v_unused_3578_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3579_);
v___x_3569_ = v_code_3432_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_dec(v_code_3432_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v_a_3546_);
lean_ctor_set(v___x_3569_, 0, v_a_3544_);
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3544_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_a_3546_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3574_; 
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v___x_3572_);
v___x_3574_ = v___x_3548_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
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
else
{
lean_object* v___x_3581_; 
lean_dec(v_a_3546_);
lean_dec(v_a_3544_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v_code_3432_);
v___x_3581_ = v___x_3548_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_code_3432_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
else
{
lean_dec(v_a_3544_);
lean_dec_ref_known(v_code_3432_, 2);
return v___x_3545_;
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec_ref_known(v_code_3432_, 2);
v_a_3584_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3543_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3543_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
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
case 3:
{
lean_object* v_fvarId_3592_; lean_object* v_args_3593_; lean_object* v___x_3594_; 
v_fvarId_3592_ = lean_ctor_get(v_code_3432_, 0);
v_args_3593_ = lean_ctor_get(v_code_3432_, 1);
lean_inc(v_fvarId_3592_);
v___x_3594_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_3592_, v_t_3431_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_fvarId_3595_; lean_object* v___x_3596_; 
v_fvarId_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_fvarId_3595_);
lean_dec_ref_known(v___x_3594_, 1);
lean_inc_ref(v_args_3593_);
v___x_3596_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3430_, v_t_3431_, v_args_3593_, v_a_3433_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3632_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3632_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3632_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
uint8_t v___x_3601_; 
v___x_3601_ = l_Lean_instBEqFVarId_beq(v_fvarId_3592_, v_fvarId_3595_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3611_; 
v_isSharedCheck_3611_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; lean_object* v_unused_3613_; 
v_unused_3612_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3613_);
v___x_3603_ = v_code_3432_;
v_isShared_3604_ = v_isSharedCheck_3611_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v_code_3432_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3611_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v_a_3597_);
lean_ctor_set(v___x_3603_, 0, v_fvarId_3595_);
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_fvarId_3595_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_a_3597_);
v___x_3606_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3606_);
v___x_3608_ = v___x_3599_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
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
size_t v___x_3614_; size_t v___x_3615_; uint8_t v___x_3616_; 
v___x_3614_ = lean_ptr_addr(v_args_3593_);
v___x_3615_ = lean_ptr_addr(v_a_3597_);
v___x_3616_ = lean_usize_dec_eq(v___x_3614_, v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3626_; 
v_isSharedCheck_3626_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; lean_object* v_unused_3628_; 
v_unused_3627_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3628_);
v___x_3618_ = v_code_3432_;
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
else
{
lean_dec(v_code_3432_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 1, v_a_3597_);
lean_ctor_set(v___x_3618_, 0, v_fvarId_3595_);
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_fvarId_3595_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_a_3597_);
v___x_3621_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3621_);
v___x_3623_ = v___x_3599_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_object* v___x_3630_; 
lean_dec(v_a_3597_);
lean_dec(v_fvarId_3595_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v_code_3432_);
v___x_3630_ = v___x_3599_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_code_3432_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_fvarId_3595_);
lean_dec_ref_known(v_code_3432_, 2);
v_a_3633_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3596_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3596_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
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
else
{
lean_object* v___x_3641_; 
lean_dec_ref_known(v_code_3432_, 2);
v___x_3641_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3641_;
}
}
case 4:
{
lean_object* v_cases_3642_; lean_object* v_typeName_3643_; lean_object* v_resultType_3644_; lean_object* v_discr_3645_; lean_object* v_alts_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3691_; 
v_cases_3642_ = lean_ctor_get(v_code_3432_, 0);
lean_inc_ref(v_cases_3642_);
v_typeName_3643_ = lean_ctor_get(v_cases_3642_, 0);
v_resultType_3644_ = lean_ctor_get(v_cases_3642_, 1);
v_discr_3645_ = lean_ctor_get(v_cases_3642_, 2);
v_alts_3646_ = lean_ctor_get(v_cases_3642_, 3);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_cases_3642_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3648_ = v_cases_3642_;
v_isShared_3649_ = v_isSharedCheck_3691_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_alts_3646_);
lean_inc(v_discr_3645_);
lean_inc(v_resultType_3644_);
lean_inc(v_typeName_3643_);
lean_dec(v_cases_3642_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3691_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_inc_ref(v_resultType_3644_);
v___x_3650_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3430_, v_a_3433_, v_t_3431_, v_resultType_3644_);
lean_inc(v_discr_3645_);
v___x_3651_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_discr_3645_, v_t_3431_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_fvarId_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3689_; 
v_fvarId_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3689_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_fvarId_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3689_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3646_);
v___x_3657_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3430_, v_t_3431_, v___x_3656_, v_alts_3646_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3680_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3680_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3680_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
size_t v___x_3672_; size_t v___x_3673_; uint8_t v___x_3674_; 
v___x_3672_ = lean_ptr_addr(v_alts_3646_);
lean_dec_ref(v_alts_3646_);
v___x_3673_ = lean_ptr_addr(v_a_3658_);
v___x_3674_ = lean_usize_dec_eq(v___x_3672_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_dec(v_discr_3645_);
lean_dec_ref(v_resultType_3644_);
lean_dec_ref_known(v_code_3432_, 1);
goto v___jp_3662_;
}
else
{
size_t v___x_3675_; size_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3675_ = lean_ptr_addr(v_resultType_3644_);
lean_dec_ref(v_resultType_3644_);
v___x_3676_ = lean_ptr_addr(v___x_3650_);
v___x_3677_ = lean_usize_dec_eq(v___x_3675_, v___x_3676_);
if (v___x_3677_ == 0)
{
lean_dec(v_discr_3645_);
lean_dec_ref_known(v_code_3432_, 1);
goto v___jp_3662_;
}
else
{
uint8_t v___x_3678_; 
v___x_3678_ = l_Lean_instBEqFVarId_beq(v_discr_3645_, v_fvarId_3652_);
lean_dec(v_discr_3645_);
if (v___x_3678_ == 0)
{
lean_dec_ref_known(v_code_3432_, 1);
goto v___jp_3662_;
}
else
{
lean_object* v___x_3679_; 
lean_del_object(v___x_3660_);
lean_dec(v_a_3658_);
lean_del_object(v___x_3654_);
lean_dec(v_fvarId_3652_);
lean_dec_ref(v___x_3650_);
lean_del_object(v___x_3648_);
lean_dec(v_typeName_3643_);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v_code_3432_);
return v___x_3679_;
}
}
}
v___jp_3662_:
{
lean_object* v___x_3664_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 3, v_a_3658_);
lean_ctor_set(v___x_3648_, 2, v_fvarId_3652_);
lean_ctor_set(v___x_3648_, 1, v___x_3650_);
v___x_3664_ = v___x_3648_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_typeName_3643_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_fvarId_3652_);
lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_a_3658_);
v___x_3664_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 4);
lean_ctor_set(v___x_3654_, 0, v___x_3664_);
v___x_3666_ = v___x_3654_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3666_);
v___x_3668_ = v___x_3660_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3654_);
lean_dec(v_fvarId_3652_);
lean_dec_ref(v___x_3650_);
lean_del_object(v___x_3648_);
lean_dec_ref(v_alts_3646_);
lean_dec(v_discr_3645_);
lean_dec_ref(v_resultType_3644_);
lean_dec(v_typeName_3643_);
lean_dec_ref_known(v_code_3432_, 1);
v_a_3681_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3657_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3657_);
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
lean_dec_ref(v___x_3650_);
lean_del_object(v___x_3648_);
lean_dec_ref(v_alts_3646_);
lean_dec(v_discr_3645_);
lean_dec_ref(v_resultType_3644_);
lean_dec(v_typeName_3643_);
lean_dec_ref_known(v_code_3432_, 1);
v___x_3690_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3690_;
}
}
}
case 5:
{
lean_object* v_fvarId_3692_; lean_object* v___x_3693_; 
v_fvarId_3692_ = lean_ctor_get(v_code_3432_, 0);
lean_inc(v_fvarId_3692_);
v___x_3693_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_3692_, v_t_3431_);
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
v_isSharedCheck_3708_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3709_);
v___x_3700_ = v_code_3432_;
v_isShared_3701_ = v_isSharedCheck_3708_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v_code_3432_);
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
lean_ctor_set(v___x_3696_, 0, v_code_3432_);
v___x_3711_ = v___x_3696_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_code_3432_);
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
lean_dec_ref_known(v_code_3432_, 1);
v___x_3714_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3714_;
}
}
case 6:
{
lean_object* v_type_3715_; lean_object* v___x_3716_; size_t v___x_3717_; size_t v___x_3718_; uint8_t v___x_3719_; 
v_type_3715_ = lean_ctor_get(v_code_3432_, 0);
lean_inc_ref(v_type_3715_);
v___x_3716_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3430_, v_a_3433_, v_t_3431_, v_type_3715_);
v___x_3717_ = lean_ptr_addr(v_type_3715_);
v___x_3718_ = lean_ptr_addr(v___x_3716_);
v___x_3719_ = lean_usize_dec_eq(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3727_; 
v_isSharedCheck_3727_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3728_);
v___x_3721_ = v_code_3432_;
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
else
{
lean_dec(v_code_3432_);
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
lean_ctor_set(v___x_3729_, 0, v_code_3432_);
return v___x_3729_;
}
}
case 7:
{
lean_object* v_fvarId_3730_; lean_object* v_i_3731_; lean_object* v_y_3732_; lean_object* v_k_3733_; lean_object* v___x_3734_; 
v_fvarId_3730_ = lean_ctor_get(v_code_3432_, 0);
v_i_3731_ = lean_ctor_get(v_code_3432_, 1);
v_y_3732_ = lean_ctor_get(v_code_3432_, 2);
v_k_3733_ = lean_ctor_get(v_code_3432_, 3);
lean_inc(v_fvarId_3730_);
v___x_3734_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_3730_, v_t_3431_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_fvarId_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_fvarId_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_fvarId_3735_);
lean_dec_ref_known(v___x_3734_, 1);
lean_inc(v_y_3732_);
v___x_3736_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3430_, v_a_3433_, v_y_3732_, v_t_3431_);
lean_inc_ref(v_k_3733_);
v___x_3737_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_3733_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3811_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3740_ = v___x_3737_;
v_isShared_3741_ = v_isSharedCheck_3811_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3811_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
size_t v___x_3742_; size_t v___x_3743_; uint8_t v___x_3744_; 
v___x_3742_ = lean_ptr_addr(v_fvarId_3730_);
v___x_3743_ = lean_ptr_addr(v_fvarId_3735_);
v___x_3744_ = lean_usize_dec_eq(v___x_3742_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3754_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; 
v_unused_3755_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3758_);
v___x_3746_ = v_code_3432_;
v_isShared_3747_ = v_isSharedCheck_3754_;
goto v_resetjp_3745_;
}
else
{
lean_dec(v_code_3432_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3754_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 3, v_a_3738_);
lean_ctor_set(v___x_3746_, 2, v___x_3736_);
lean_ctor_set(v___x_3746_, 0, v_fvarId_3735_);
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_a_3738_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3749_);
v___x_3751_ = v___x_3740_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_nat_dec_eq(v_i_3731_, v_i_3731_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3769_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; lean_object* v_unused_3771_; lean_object* v_unused_3772_; lean_object* v_unused_3773_; 
v_unused_3770_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3773_);
v___x_3761_ = v_code_3432_;
v_isShared_3762_ = v_isSharedCheck_3769_;
goto v_resetjp_3760_;
}
else
{
lean_dec(v_code_3432_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3769_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 3, v_a_3738_);
lean_ctor_set(v___x_3761_, 2, v___x_3736_);
lean_ctor_set(v___x_3761_, 0, v_fvarId_3735_);
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_a_3738_);
v___x_3764_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3766_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3764_);
v___x_3766_ = v___x_3740_;
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
v___x_3774_ = lean_ptr_addr(v_y_3732_);
v___x_3775_ = lean_ptr_addr(v___x_3736_);
v___x_3776_ = lean_usize_dec_eq(v___x_3774_, v___x_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3786_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3786_ == 0)
{
lean_object* v_unused_3787_; lean_object* v_unused_3788_; lean_object* v_unused_3789_; lean_object* v_unused_3790_; 
v_unused_3787_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3788_);
v_unused_3789_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3790_);
v___x_3778_ = v_code_3432_;
v_isShared_3779_ = v_isSharedCheck_3786_;
goto v_resetjp_3777_;
}
else
{
lean_dec(v_code_3432_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3786_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 3, v_a_3738_);
lean_ctor_set(v___x_3778_, 2, v___x_3736_);
lean_ctor_set(v___x_3778_, 0, v_fvarId_3735_);
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v_a_3738_);
v___x_3781_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3783_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3781_);
v___x_3783_ = v___x_3740_;
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
size_t v___x_3791_; size_t v___x_3792_; uint8_t v___x_3793_; 
v___x_3791_ = lean_ptr_addr(v_k_3733_);
v___x_3792_ = lean_ptr_addr(v_a_3738_);
v___x_3793_ = lean_usize_dec_eq(v___x_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3803_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; lean_object* v_unused_3807_; 
v_unused_3804_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3807_);
v___x_3795_ = v_code_3432_;
v_isShared_3796_ = v_isSharedCheck_3803_;
goto v_resetjp_3794_;
}
else
{
lean_dec(v_code_3432_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3803_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 3, v_a_3738_);
lean_ctor_set(v___x_3795_, 2, v___x_3736_);
lean_ctor_set(v___x_3795_, 0, v_fvarId_3735_);
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3802_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3802_, 3, v_a_3738_);
v___x_3798_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3800_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3798_);
v___x_3800_ = v___x_3740_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v___x_3809_; 
lean_dec(v_a_3738_);
lean_dec(v___x_3736_);
lean_dec(v_fvarId_3735_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v_code_3432_);
v___x_3809_ = v___x_3740_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_code_3432_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
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
lean_dec_ref_known(v_code_3432_, 4);
return v___x_3737_;
}
}
else
{
lean_object* v___x_3812_; 
lean_dec_ref_known(v_code_3432_, 4);
v___x_3812_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3812_;
}
}
case 8:
{
lean_object* v_fvarId_3813_; lean_object* v_i_3814_; lean_object* v_y_3815_; lean_object* v_k_3816_; lean_object* v___x_3817_; 
v_fvarId_3813_ = lean_ctor_get(v_code_3432_, 0);
v_i_3814_ = lean_ctor_get(v_code_3432_, 1);
v_y_3815_ = lean_ctor_get(v_code_3432_, 2);
v_k_3816_ = lean_ctor_get(v_code_3432_, 3);
lean_inc(v_fvarId_3813_);
v___x_3817_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_3813_, v_t_3431_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_fvarId_3818_; lean_object* v___x_3819_; 
v_fvarId_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_fvarId_3818_);
lean_dec_ref_known(v___x_3817_, 1);
lean_inc(v_y_3815_);
v___x_3819_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_y_3815_, v_t_3431_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_fvarId_3820_; lean_object* v___x_3821_; 
v_fvarId_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_fvarId_3820_);
lean_dec_ref_known(v___x_3819_, 1);
lean_inc_ref(v_k_3816_);
v___x_3821_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_3816_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3895_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3895_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3895_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
size_t v___x_3826_; size_t v___x_3827_; uint8_t v___x_3828_; 
v___x_3826_ = lean_ptr_addr(v_fvarId_3813_);
v___x_3827_ = lean_ptr_addr(v_fvarId_3818_);
v___x_3828_ = lean_usize_dec_eq(v___x_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3838_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; lean_object* v_unused_3842_; 
v_unused_3839_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3842_);
v___x_3830_ = v_code_3432_;
v_isShared_3831_ = v_isSharedCheck_3838_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v_code_3432_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3838_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 3, v_a_3822_);
lean_ctor_set(v___x_3830_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3830_, 0, v_fvarId_3818_);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3837_, 3, v_a_3822_);
v___x_3833_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3835_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3833_);
v___x_3835_ = v___x_3824_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
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
uint8_t v___x_3843_; 
v___x_3843_ = lean_nat_dec_eq(v_i_3814_, v_i_3814_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3853_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; 
v_unused_3854_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3857_);
v___x_3845_ = v_code_3432_;
v_isShared_3846_ = v_isSharedCheck_3853_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v_code_3432_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3853_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 3, v_a_3822_);
lean_ctor_set(v___x_3845_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3845_, 0, v_fvarId_3818_);
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3852_, 3, v_a_3822_);
v___x_3848_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3850_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3848_);
v___x_3850_ = v___x_3824_;
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
v___x_3858_ = lean_ptr_addr(v_y_3815_);
v___x_3859_ = lean_ptr_addr(v_fvarId_3820_);
v___x_3860_ = lean_usize_dec_eq(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3870_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3871_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3874_);
v___x_3862_ = v_code_3432_;
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
else
{
lean_dec(v_code_3432_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 3, v_a_3822_);
lean_ctor_set(v___x_3862_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3862_, 0, v_fvarId_3818_);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_a_3822_);
v___x_3865_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3865_);
v___x_3867_ = v___x_3824_;
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
size_t v___x_3875_; size_t v___x_3876_; uint8_t v___x_3877_; 
v___x_3875_ = lean_ptr_addr(v_k_3816_);
v___x_3876_ = lean_ptr_addr(v_a_3822_);
v___x_3877_ = lean_usize_dec_eq(v___x_3875_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3887_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; 
v_unused_3888_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3891_);
v___x_3879_ = v_code_3432_;
v_isShared_3880_ = v_isSharedCheck_3887_;
goto v_resetjp_3878_;
}
else
{
lean_dec(v_code_3432_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3887_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 3, v_a_3822_);
lean_ctor_set(v___x_3879_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3879_, 0, v_fvarId_3818_);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v_a_3822_);
v___x_3882_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3882_);
v___x_3884_ = v___x_3824_;
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
lean_object* v___x_3893_; 
lean_dec(v_a_3822_);
lean_dec(v_fvarId_3820_);
lean_dec(v_fvarId_3818_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v_code_3432_);
v___x_3893_ = v___x_3824_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_code_3432_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
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
lean_dec_ref_known(v_code_3432_, 4);
return v___x_3821_;
}
}
else
{
lean_object* v___x_3896_; 
lean_dec(v_fvarId_3818_);
lean_dec_ref_known(v_code_3432_, 4);
v___x_3896_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3896_;
}
}
else
{
lean_object* v___x_3897_; 
lean_dec_ref_known(v_code_3432_, 4);
v___x_3897_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3897_;
}
}
case 9:
{
lean_object* v_fvarId_3898_; lean_object* v_i_3899_; lean_object* v_offset_3900_; lean_object* v_y_3901_; lean_object* v_ty_3902_; lean_object* v_k_3903_; lean_object* v___x_3904_; 
v_fvarId_3898_ = lean_ctor_get(v_code_3432_, 0);
v_i_3899_ = lean_ctor_get(v_code_3432_, 1);
v_offset_3900_ = lean_ctor_get(v_code_3432_, 2);
v_y_3901_ = lean_ctor_get(v_code_3432_, 3);
v_ty_3902_ = lean_ctor_get(v_code_3432_, 4);
v_k_3903_ = lean_ctor_get(v_code_3432_, 5);
lean_inc(v_fvarId_3898_);
v___x_3904_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_3898_, v_t_3431_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_fvarId_3905_; lean_object* v___x_3906_; 
v_fvarId_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_fvarId_3905_);
lean_dec_ref_known(v___x_3904_, 1);
lean_inc(v_y_3901_);
v___x_3906_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_y_3901_, v_t_3431_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_fvarId_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_fvarId_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_fvarId_3907_);
lean_dec_ref_known(v___x_3906_, 1);
lean_inc_ref(v_ty_3902_);
v___x_3908_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3430_, v_a_3433_, v_t_3431_, v_ty_3902_);
lean_inc_ref(v_k_3903_);
v___x_3909_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_3903_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_4027_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_4027_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_4027_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
size_t v___x_3914_; size_t v___x_3915_; uint8_t v___x_3916_; 
v___x_3914_ = lean_ptr_addr(v_fvarId_3898_);
v___x_3915_ = lean_ptr_addr(v_fvarId_3905_);
v___x_3916_ = lean_usize_dec_eq(v___x_3914_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3926_; 
lean_inc(v_offset_3900_);
lean_inc(v_i_3899_);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; lean_object* v_unused_3928_; lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; 
v_unused_3927_ = lean_ctor_get(v_code_3432_, 5);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_code_3432_, 4);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3932_);
v___x_3918_ = v_code_3432_;
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
else
{
lean_dec(v_code_3432_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 5, v_a_3910_);
lean_ctor_set(v___x_3918_, 4, v___x_3908_);
lean_ctor_set(v___x_3918_, 3, v_fvarId_3907_);
lean_ctor_set(v___x_3918_, 0, v_fvarId_3905_);
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fvarId_3905_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_i_3899_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_offset_3900_);
lean_ctor_set(v_reuseFailAlloc_3925_, 3, v_fvarId_3907_);
lean_ctor_set(v_reuseFailAlloc_3925_, 4, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3925_, 5, v_a_3910_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3921_);
v___x_3923_ = v___x_3912_;
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
v___x_3933_ = lean_nat_dec_eq(v_i_3899_, v_i_3899_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3943_; 
lean_inc(v_offset_3900_);
lean_inc(v_i_3899_);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; 
v_unused_3944_ = lean_ctor_get(v_code_3432_, 5);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_code_3432_, 4);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3949_);
v___x_3935_ = v_code_3432_;
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v_code_3432_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 5, v_a_3910_);
lean_ctor_set(v___x_3935_, 4, v___x_3908_);
lean_ctor_set(v___x_3935_, 3, v_fvarId_3907_);
lean_ctor_set(v___x_3935_, 0, v_fvarId_3905_);
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_fvarId_3905_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_i_3899_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_offset_3900_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v_fvarId_3907_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3942_, 5, v_a_3910_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3938_);
v___x_3940_ = v___x_3912_;
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
uint8_t v___x_3950_; 
v___x_3950_ = lean_nat_dec_eq(v_offset_3900_, v_offset_3900_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3960_; 
lean_inc(v_offset_3900_);
lean_inc(v_i_3899_);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3960_ == 0)
{
lean_object* v_unused_3961_; lean_object* v_unused_3962_; lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; 
v_unused_3961_ = lean_ctor_get(v_code_3432_, 5);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_code_3432_, 4);
lean_dec(v_unused_3962_);
v_unused_3963_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3966_);
v___x_3952_ = v_code_3432_;
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
else
{
lean_dec(v_code_3432_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 5, v_a_3910_);
lean_ctor_set(v___x_3952_, 4, v___x_3908_);
lean_ctor_set(v___x_3952_, 3, v_fvarId_3907_);
lean_ctor_set(v___x_3952_, 0, v_fvarId_3905_);
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_fvarId_3905_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_i_3899_);
lean_ctor_set(v_reuseFailAlloc_3959_, 2, v_offset_3900_);
lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_fvarId_3907_);
lean_ctor_set(v_reuseFailAlloc_3959_, 4, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3959_, 5, v_a_3910_);
v___x_3955_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3957_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3955_);
v___x_3957_ = v___x_3912_;
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
v___x_3967_ = lean_ptr_addr(v_y_3901_);
v___x_3968_ = lean_ptr_addr(v_fvarId_3907_);
v___x_3969_ = lean_usize_dec_eq(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3979_; 
lean_inc(v_offset_3900_);
lean_inc(v_i_3899_);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3979_ == 0)
{
lean_object* v_unused_3980_; lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3980_ = lean_ctor_get(v_code_3432_, 5);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_code_3432_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_3985_);
v___x_3971_ = v_code_3432_;
v_isShared_3972_ = v_isSharedCheck_3979_;
goto v_resetjp_3970_;
}
else
{
lean_dec(v_code_3432_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3979_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 5, v_a_3910_);
lean_ctor_set(v___x_3971_, 4, v___x_3908_);
lean_ctor_set(v___x_3971_, 3, v_fvarId_3907_);
lean_ctor_set(v___x_3971_, 0, v_fvarId_3905_);
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_fvarId_3905_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_i_3899_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_offset_3900_);
lean_ctor_set(v_reuseFailAlloc_3978_, 3, v_fvarId_3907_);
lean_ctor_set(v_reuseFailAlloc_3978_, 4, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3978_, 5, v_a_3910_);
v___x_3974_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3976_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3974_);
v___x_3976_ = v___x_3912_;
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
v___x_3986_ = lean_ptr_addr(v_ty_3902_);
v___x_3987_ = lean_ptr_addr(v___x_3908_);
v___x_3988_ = lean_usize_dec_eq(v___x_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3998_; 
lean_inc(v_offset_3900_);
lean_inc(v_i_3899_);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; 
v_unused_3999_ = lean_ctor_get(v_code_3432_, 5);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_code_3432_, 4);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4004_);
v___x_3990_ = v_code_3432_;
v_isShared_3991_ = v_isSharedCheck_3998_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v_code_3432_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3998_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 5, v_a_3910_);
lean_ctor_set(v___x_3990_, 4, v___x_3908_);
lean_ctor_set(v___x_3990_, 3, v_fvarId_3907_);
lean_ctor_set(v___x_3990_, 0, v_fvarId_3905_);
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fvarId_3905_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_i_3899_);
lean_ctor_set(v_reuseFailAlloc_3997_, 2, v_offset_3900_);
lean_ctor_set(v_reuseFailAlloc_3997_, 3, v_fvarId_3907_);
lean_ctor_set(v_reuseFailAlloc_3997_, 4, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3997_, 5, v_a_3910_);
v___x_3993_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3995_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3993_);
v___x_3995_ = v___x_3912_;
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
size_t v___x_4005_; size_t v___x_4006_; uint8_t v___x_4007_; 
v___x_4005_ = lean_ptr_addr(v_k_3903_);
v___x_4006_ = lean_ptr_addr(v_a_3910_);
v___x_4007_ = lean_usize_dec_eq(v___x_4005_, v___x_4006_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4017_; 
lean_inc(v_offset_3900_);
lean_inc(v_i_3899_);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4017_ == 0)
{
lean_object* v_unused_4018_; lean_object* v_unused_4019_; lean_object* v_unused_4020_; lean_object* v_unused_4021_; lean_object* v_unused_4022_; lean_object* v_unused_4023_; 
v_unused_4018_ = lean_ctor_get(v_code_3432_, 5);
lean_dec(v_unused_4018_);
v_unused_4019_ = lean_ctor_get(v_code_3432_, 4);
lean_dec(v_unused_4019_);
v_unused_4020_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_4020_);
v_unused_4021_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4021_);
v_unused_4022_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4022_);
v_unused_4023_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4023_);
v___x_4009_ = v_code_3432_;
v_isShared_4010_ = v_isSharedCheck_4017_;
goto v_resetjp_4008_;
}
else
{
lean_dec(v_code_3432_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4017_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 5, v_a_3910_);
lean_ctor_set(v___x_4009_, 4, v___x_3908_);
lean_ctor_set(v___x_4009_, 3, v_fvarId_3907_);
lean_ctor_set(v___x_4009_, 0, v_fvarId_3905_);
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_fvarId_3905_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_i_3899_);
lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_offset_3900_);
lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_fvarId_3907_);
lean_ctor_set(v_reuseFailAlloc_4016_, 4, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_4016_, 5, v_a_3910_);
v___x_4012_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4014_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_4012_);
v___x_4014_ = v___x_3912_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
lean_object* v___x_4025_; 
lean_dec(v_a_3910_);
lean_dec_ref(v___x_3908_);
lean_dec(v_fvarId_3907_);
lean_dec(v_fvarId_3905_);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v_code_3432_);
v___x_4025_ = v___x_3912_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_code_3432_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
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
lean_dec_ref(v___x_3908_);
lean_dec(v_fvarId_3907_);
lean_dec(v_fvarId_3905_);
lean_dec_ref_known(v_code_3432_, 6);
return v___x_3909_;
}
}
else
{
lean_object* v___x_4028_; 
lean_dec(v_fvarId_3905_);
lean_dec_ref_known(v_code_3432_, 6);
v___x_4028_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_4028_;
}
}
else
{
lean_object* v___x_4029_; 
lean_dec_ref_known(v_code_3432_, 6);
v___x_4029_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_4029_;
}
}
case 10:
{
lean_object* v_fvarId_4030_; lean_object* v_cidx_4031_; lean_object* v_k_4032_; lean_object* v___x_4033_; 
v_fvarId_4030_ = lean_ctor_get(v_code_3432_, 0);
v_cidx_4031_ = lean_ctor_get(v_code_3432_, 1);
v_k_4032_ = lean_ctor_get(v_code_3432_, 2);
lean_inc(v_fvarId_4030_);
v___x_4033_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_4030_, v_t_3431_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_fvarId_4034_; lean_object* v___x_4035_; 
v_fvarId_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_fvarId_4034_);
lean_dec_ref_known(v___x_4033_, 1);
lean_inc_ref(v_k_4032_);
v___x_4035_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_4032_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4089_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4089_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4089_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
size_t v___x_4040_; size_t v___x_4041_; uint8_t v___x_4042_; 
v___x_4040_ = lean_ptr_addr(v_fvarId_4030_);
v___x_4041_ = lean_ptr_addr(v_fvarId_4034_);
v___x_4042_ = lean_usize_dec_eq(v___x_4040_, v___x_4041_);
if (v___x_4042_ == 0)
{
lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4052_; 
lean_inc(v_cidx_4031_);
v_isSharedCheck_4052_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4052_ == 0)
{
lean_object* v_unused_4053_; lean_object* v_unused_4054_; lean_object* v_unused_4055_; 
v_unused_4053_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4053_);
v_unused_4054_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4054_);
v_unused_4055_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4055_);
v___x_4044_ = v_code_3432_;
v_isShared_4045_ = v_isSharedCheck_4052_;
goto v_resetjp_4043_;
}
else
{
lean_dec(v_code_3432_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4052_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 2, v_a_4036_);
lean_ctor_set(v___x_4044_, 0, v_fvarId_4034_);
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_fvarId_4034_);
lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_cidx_4031_);
lean_ctor_set(v_reuseFailAlloc_4051_, 2, v_a_4036_);
v___x_4047_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4049_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4047_);
v___x_4049_ = v___x_4038_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4047_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
uint8_t v___x_4056_; 
v___x_4056_ = lean_nat_dec_eq(v_cidx_4031_, v_cidx_4031_);
if (v___x_4056_ == 0)
{
lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4066_; 
lean_inc(v_cidx_4031_);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; lean_object* v_unused_4068_; lean_object* v_unused_4069_; 
v_unused_4067_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4069_);
v___x_4058_ = v_code_3432_;
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
else
{
lean_dec(v_code_3432_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 2, v_a_4036_);
lean_ctor_set(v___x_4058_, 0, v_fvarId_4034_);
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_fvarId_4034_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_cidx_4031_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_a_4036_);
v___x_4061_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4061_);
v___x_4063_ = v___x_4038_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
size_t v___x_4070_; size_t v___x_4071_; uint8_t v___x_4072_; 
v___x_4070_ = lean_ptr_addr(v_k_4032_);
v___x_4071_ = lean_ptr_addr(v_a_4036_);
v___x_4072_ = lean_usize_dec_eq(v___x_4070_, v___x_4071_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4082_; 
lean_inc(v_cidx_4031_);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; lean_object* v_unused_4084_; lean_object* v_unused_4085_; 
v_unused_4083_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4083_);
v_unused_4084_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4085_);
v___x_4074_ = v_code_3432_;
v_isShared_4075_ = v_isSharedCheck_4082_;
goto v_resetjp_4073_;
}
else
{
lean_dec(v_code_3432_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4082_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 2, v_a_4036_);
lean_ctor_set(v___x_4074_, 0, v_fvarId_4034_);
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_fvarId_4034_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_cidx_4031_);
lean_ctor_set(v_reuseFailAlloc_4081_, 2, v_a_4036_);
v___x_4077_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4079_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4077_);
v___x_4079_ = v___x_4038_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v___x_4087_; 
lean_dec(v_a_4036_);
lean_dec(v_fvarId_4034_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v_code_3432_);
v___x_4087_ = v___x_4038_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_code_3432_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4034_);
lean_dec_ref_known(v_code_3432_, 3);
return v___x_4035_;
}
}
else
{
lean_object* v___x_4090_; 
lean_dec_ref_known(v_code_3432_, 3);
v___x_4090_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_4090_;
}
}
case 11:
{
lean_object* v_fvarId_4091_; lean_object* v_n_4092_; uint8_t v_check_4093_; uint8_t v_persistent_4094_; lean_object* v_k_4095_; lean_object* v___x_4096_; 
v_fvarId_4091_ = lean_ctor_get(v_code_3432_, 0);
v_n_4092_ = lean_ctor_get(v_code_3432_, 1);
v_check_4093_ = lean_ctor_get_uint8(v_code_3432_, sizeof(void*)*3);
v_persistent_4094_ = lean_ctor_get_uint8(v_code_3432_, sizeof(void*)*3 + 1);
v_k_4095_ = lean_ctor_get(v_code_3432_, 2);
lean_inc(v_fvarId_4091_);
v___x_4096_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_4091_, v_t_3431_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_fvarId_4097_; lean_object* v___x_4098_; 
v_fvarId_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_fvarId_4097_);
lean_dec_ref_known(v___x_4096_, 1);
lean_inc_ref(v_k_4095_);
v___x_4098_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_4095_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4152_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4152_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4152_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
size_t v___x_4103_; size_t v___x_4104_; uint8_t v___x_4105_; 
v___x_4103_ = lean_ptr_addr(v_fvarId_4091_);
v___x_4104_ = lean_ptr_addr(v_fvarId_4097_);
v___x_4105_ = lean_usize_dec_eq(v___x_4103_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4115_; 
lean_inc(v_n_4092_);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; lean_object* v_unused_4117_; lean_object* v_unused_4118_; 
v_unused_4116_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4117_);
v_unused_4118_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4118_);
v___x_4107_ = v_code_3432_;
v_isShared_4108_ = v_isSharedCheck_4115_;
goto v_resetjp_4106_;
}
else
{
lean_dec(v_code_3432_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4115_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 2, v_a_4099_);
lean_ctor_set(v___x_4107_, 0, v_fvarId_4097_);
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_fvarId_4097_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_n_4092_);
lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_a_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4114_, sizeof(void*)*3, v_check_4093_);
lean_ctor_set_uint8(v_reuseFailAlloc_4114_, sizeof(void*)*3 + 1, v_persistent_4094_);
v___x_4110_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4112_; 
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4110_);
v___x_4112_ = v___x_4101_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
uint8_t v___x_4119_; 
v___x_4119_ = lean_nat_dec_eq(v_n_4092_, v_n_4092_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4129_; 
lean_inc(v_n_4092_);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4129_ == 0)
{
lean_object* v_unused_4130_; lean_object* v_unused_4131_; lean_object* v_unused_4132_; 
v_unused_4130_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4131_);
v_unused_4132_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4132_);
v___x_4121_ = v_code_3432_;
v_isShared_4122_ = v_isSharedCheck_4129_;
goto v_resetjp_4120_;
}
else
{
lean_dec(v_code_3432_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4129_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 2, v_a_4099_);
lean_ctor_set(v___x_4121_, 0, v_fvarId_4097_);
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_fvarId_4097_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_n_4092_);
lean_ctor_set(v_reuseFailAlloc_4128_, 2, v_a_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4128_, sizeof(void*)*3, v_check_4093_);
lean_ctor_set_uint8(v_reuseFailAlloc_4128_, sizeof(void*)*3 + 1, v_persistent_4094_);
v___x_4124_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4126_; 
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4124_);
v___x_4126_ = v___x_4101_;
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
v___x_4133_ = lean_ptr_addr(v_k_4095_);
v___x_4134_ = lean_ptr_addr(v_a_4099_);
v___x_4135_ = lean_usize_dec_eq(v___x_4133_, v___x_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4145_; 
lean_inc(v_n_4092_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; lean_object* v_unused_4147_; lean_object* v_unused_4148_; 
v_unused_4146_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4146_);
v_unused_4147_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4148_);
v___x_4137_ = v_code_3432_;
v_isShared_4138_ = v_isSharedCheck_4145_;
goto v_resetjp_4136_;
}
else
{
lean_dec(v_code_3432_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4145_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 2, v_a_4099_);
lean_ctor_set(v___x_4137_, 0, v_fvarId_4097_);
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_fvarId_4097_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_n_4092_);
lean_ctor_set(v_reuseFailAlloc_4144_, 2, v_a_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4144_, sizeof(void*)*3, v_check_4093_);
lean_ctor_set_uint8(v_reuseFailAlloc_4144_, sizeof(void*)*3 + 1, v_persistent_4094_);
v___x_4140_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4142_; 
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4140_);
v___x_4142_ = v___x_4101_;
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
lean_dec(v_a_4099_);
lean_dec(v_fvarId_4097_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v_code_3432_);
v___x_4150_ = v___x_4101_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_code_3432_);
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
lean_dec(v_fvarId_4097_);
lean_dec_ref_known(v_code_3432_, 3);
return v___x_4098_;
}
}
else
{
lean_object* v___x_4153_; 
lean_dec_ref_known(v_code_3432_, 3);
v___x_4153_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_4153_;
}
}
case 12:
{
lean_object* v_fvarId_4154_; lean_object* v_n_4155_; uint8_t v_check_4156_; uint8_t v_persistent_4157_; lean_object* v_objs_x3f_4158_; lean_object* v_k_4159_; lean_object* v___x_4160_; 
v_fvarId_4154_ = lean_ctor_get(v_code_3432_, 0);
v_n_4155_ = lean_ctor_get(v_code_3432_, 1);
v_check_4156_ = lean_ctor_get_uint8(v_code_3432_, sizeof(void*)*4);
v_persistent_4157_ = lean_ctor_get_uint8(v_code_3432_, sizeof(void*)*4 + 1);
v_objs_x3f_4158_ = lean_ctor_get(v_code_3432_, 2);
v_k_4159_ = lean_ctor_get(v_code_3432_, 3);
lean_inc(v_fvarId_4154_);
v___x_4160_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_4154_, v_t_3431_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_fvarId_4161_; lean_object* v___x_4162_; 
v_fvarId_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_fvarId_4161_);
lean_dec_ref_known(v___x_4160_, 1);
lean_inc_ref(v_k_4159_);
v___x_4162_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_4159_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4236_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4236_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4236_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
size_t v___x_4167_; size_t v___x_4168_; uint8_t v___x_4169_; 
v___x_4167_ = lean_ptr_addr(v_fvarId_4154_);
v___x_4168_ = lean_ptr_addr(v_fvarId_4161_);
v___x_4169_ = lean_usize_dec_eq(v___x_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4179_; 
lean_inc(v_objs_x3f_4158_);
lean_inc(v_n_4155_);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; lean_object* v_unused_4181_; lean_object* v_unused_4182_; lean_object* v_unused_4183_; 
v_unused_4180_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_4180_);
v_unused_4181_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4181_);
v_unused_4182_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4183_);
v___x_4171_ = v_code_3432_;
v_isShared_4172_ = v_isSharedCheck_4179_;
goto v_resetjp_4170_;
}
else
{
lean_dec(v_code_3432_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4179_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 3, v_a_4163_);
lean_ctor_set(v___x_4171_, 0, v_fvarId_4161_);
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_fvarId_4161_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v_n_4155_);
lean_ctor_set(v_reuseFailAlloc_4178_, 2, v_objs_x3f_4158_);
lean_ctor_set(v_reuseFailAlloc_4178_, 3, v_a_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4178_, sizeof(void*)*4, v_check_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4178_, sizeof(void*)*4 + 1, v_persistent_4157_);
v___x_4174_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4176_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4174_);
v___x_4176_ = v___x_4165_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
else
{
uint8_t v___x_4184_; 
v___x_4184_ = lean_nat_dec_eq(v_n_4155_, v_n_4155_);
if (v___x_4184_ == 0)
{
lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4194_; 
lean_inc(v_objs_x3f_4158_);
lean_inc(v_n_4155_);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4194_ == 0)
{
lean_object* v_unused_4195_; lean_object* v_unused_4196_; lean_object* v_unused_4197_; lean_object* v_unused_4198_; 
v_unused_4195_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_4195_);
v_unused_4196_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4196_);
v_unused_4197_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4197_);
v_unused_4198_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4198_);
v___x_4186_ = v_code_3432_;
v_isShared_4187_ = v_isSharedCheck_4194_;
goto v_resetjp_4185_;
}
else
{
lean_dec(v_code_3432_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4194_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 3, v_a_4163_);
lean_ctor_set(v___x_4186_, 0, v_fvarId_4161_);
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_fvarId_4161_);
lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_n_4155_);
lean_ctor_set(v_reuseFailAlloc_4193_, 2, v_objs_x3f_4158_);
lean_ctor_set(v_reuseFailAlloc_4193_, 3, v_a_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4193_, sizeof(void*)*4, v_check_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4193_, sizeof(void*)*4 + 1, v_persistent_4157_);
v___x_4189_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4191_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4189_);
v___x_4191_ = v___x_4165_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4189_);
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
size_t v___x_4199_; size_t v___x_4200_; uint8_t v___x_4201_; 
v___x_4199_ = lean_ptr_addr(v_objs_x3f_4158_);
v___x_4200_ = lean_ptr_addr(v_objs_x3f_4158_);
v___x_4201_ = lean_usize_dec_eq(v___x_4199_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4211_; 
lean_inc(v_objs_x3f_4158_);
lean_inc(v_n_4155_);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; lean_object* v_unused_4213_; lean_object* v_unused_4214_; lean_object* v_unused_4215_; 
v_unused_4212_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_4212_);
v_unused_4213_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4214_);
v_unused_4215_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4215_);
v___x_4203_ = v_code_3432_;
v_isShared_4204_ = v_isSharedCheck_4211_;
goto v_resetjp_4202_;
}
else
{
lean_dec(v_code_3432_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4211_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 3, v_a_4163_);
lean_ctor_set(v___x_4203_, 0, v_fvarId_4161_);
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_fvarId_4161_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v_n_4155_);
lean_ctor_set(v_reuseFailAlloc_4210_, 2, v_objs_x3f_4158_);
lean_ctor_set(v_reuseFailAlloc_4210_, 3, v_a_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4210_, sizeof(void*)*4, v_check_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4210_, sizeof(void*)*4 + 1, v_persistent_4157_);
v___x_4206_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4208_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4206_);
v___x_4208_ = v___x_4165_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
size_t v___x_4216_; size_t v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_ptr_addr(v_k_4159_);
v___x_4217_ = lean_ptr_addr(v_a_4163_);
v___x_4218_ = lean_usize_dec_eq(v___x_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4228_; 
lean_inc(v_objs_x3f_4158_);
lean_inc(v_n_4155_);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4228_ == 0)
{
lean_object* v_unused_4229_; lean_object* v_unused_4230_; lean_object* v_unused_4231_; lean_object* v_unused_4232_; 
v_unused_4229_ = lean_ctor_get(v_code_3432_, 3);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_code_3432_, 2);
lean_dec(v_unused_4230_);
v_unused_4231_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4231_);
v_unused_4232_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4232_);
v___x_4220_ = v_code_3432_;
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_code_3432_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 3, v_a_4163_);
lean_ctor_set(v___x_4220_, 0, v_fvarId_4161_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_fvarId_4161_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_n_4155_);
lean_ctor_set(v_reuseFailAlloc_4227_, 2, v_objs_x3f_4158_);
lean_ctor_set(v_reuseFailAlloc_4227_, 3, v_a_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4227_, sizeof(void*)*4, v_check_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4227_, sizeof(void*)*4 + 1, v_persistent_4157_);
v___x_4223_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4223_);
v___x_4225_ = v___x_4165_;
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
lean_object* v___x_4234_; 
lean_dec(v_a_4163_);
lean_dec(v_fvarId_4161_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v_code_3432_);
v___x_4234_ = v___x_4165_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_code_3432_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4161_);
lean_dec_ref_known(v_code_3432_, 4);
return v___x_4162_;
}
}
else
{
lean_object* v___x_4237_; 
lean_dec_ref_known(v_code_3432_, 4);
v___x_4237_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_4237_;
}
}
default: 
{
lean_object* v_fvarId_4238_; lean_object* v_k_4239_; lean_object* v___x_4240_; 
v_fvarId_4238_ = lean_ctor_get(v_code_3432_, 0);
v_k_4239_ = lean_ctor_get(v_code_3432_, 1);
lean_inc(v_fvarId_4238_);
v___x_4240_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3433_, v_fvarId_4238_, v_t_3431_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_fvarId_4241_; lean_object* v___x_4242_; 
v_fvarId_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_fvarId_4241_);
lean_dec_ref_known(v___x_4240_, 1);
lean_inc_ref(v_k_4239_);
v___x_4242_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3430_, v_t_3431_, v_k_4239_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4280_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4280_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4280_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
size_t v___x_4247_; size_t v___x_4248_; uint8_t v___x_4249_; 
v___x_4247_ = lean_ptr_addr(v_fvarId_4238_);
v___x_4248_ = lean_ptr_addr(v_fvarId_4241_);
v___x_4249_ = lean_usize_dec_eq(v___x_4247_, v___x_4248_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4259_; 
v_isSharedCheck_4259_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; lean_object* v_unused_4261_; 
v_unused_4260_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4260_);
v_unused_4261_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4261_);
v___x_4251_ = v_code_3432_;
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
else
{
lean_dec(v_code_3432_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 1, v_a_4243_);
lean_ctor_set(v___x_4251_, 0, v_fvarId_4241_);
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_fvarId_4241_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_a_4243_);
v___x_4254_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v___x_4256_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4254_);
v___x_4256_ = v___x_4245_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
size_t v___x_4262_; size_t v___x_4263_; uint8_t v___x_4264_; 
v___x_4262_ = lean_ptr_addr(v_k_4239_);
v___x_4263_ = lean_ptr_addr(v_a_4243_);
v___x_4264_ = lean_usize_dec_eq(v___x_4262_, v___x_4263_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4274_; 
v_isSharedCheck_4274_ = !lean_is_exclusive(v_code_3432_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; lean_object* v_unused_4276_; 
v_unused_4275_ = lean_ctor_get(v_code_3432_, 1);
lean_dec(v_unused_4275_);
v_unused_4276_ = lean_ctor_get(v_code_3432_, 0);
lean_dec(v_unused_4276_);
v___x_4266_ = v_code_3432_;
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
else
{
lean_dec(v_code_3432_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 1, v_a_4243_);
lean_ctor_set(v___x_4266_, 0, v_fvarId_4241_);
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_fvarId_4241_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_a_4243_);
v___x_4269_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4271_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4269_);
v___x_4271_ = v___x_4245_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_object* v___x_4278_; 
lean_dec(v_a_4243_);
lean_dec(v_fvarId_4241_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v_code_3432_);
v___x_4278_ = v___x_4245_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_code_3432_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4241_);
lean_dec_ref_known(v_code_3432_, 2);
return v___x_4242_;
}
}
else
{
lean_object* v___x_4281_; 
lean_dec_ref_known(v_code_3432_, 2);
v___x_4281_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3430_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_4281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4282_, uint8_t v_t_4283_, lean_object* v_decl_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_params_4291_; lean_object* v_type_4292_; lean_object* v_value_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_params_4291_ = lean_ctor_get(v_decl_4284_, 2);
v_type_4292_ = lean_ctor_get(v_decl_4284_, 3);
v_value_4293_ = lean_ctor_get(v_decl_4284_, 4);
lean_inc_ref(v_type_4292_);
v___x_4294_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4282_, v_a_4285_, v_t_4283_, v_type_4292_);
lean_inc_ref(v_params_4291_);
v___x_4295_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4282_, v_t_4283_, v_params_4291_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
lean_inc_ref(v_value_4293_);
v___x_4297_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4282_, v_t_4283_, v_value_4293_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4282_, v_decl_4284_, v___x_4294_, v_a_4296_, v_a_4298_, v_a_4287_);
return v___x_4299_;
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_a_4296_);
lean_dec_ref(v___x_4294_);
lean_dec_ref(v_decl_4284_);
v_a_4300_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4297_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4297_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v___x_4294_);
lean_dec_ref(v_decl_4284_);
v_a_4308_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4295_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4295_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4316_, lean_object* v_t_4317_, lean_object* v_decl_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
uint8_t v_pu_boxed_4325_; uint8_t v_t_boxed_4326_; lean_object* v_res_4327_; 
v_pu_boxed_4325_ = lean_unbox(v_pu_4316_);
v_t_boxed_4326_ = lean_unbox(v_t_4317_);
v_res_4327_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4325_, v_t_boxed_4326_, v_decl_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec_ref(v_a_4319_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4328_, lean_object* v_t_4329_, lean_object* v_i_4330_, lean_object* v_as_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
uint8_t v_pu_boxed_4338_; uint8_t v_t_boxed_4339_; lean_object* v_res_4340_; 
v_pu_boxed_4338_ = lean_unbox(v_pu_4328_);
v_t_boxed_4339_ = lean_unbox(v_t_4329_);
v_res_4340_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4338_, v_t_boxed_4339_, v_i_4330_, v_as_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4341_, lean_object* v_t_4342_, lean_object* v_code_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
uint8_t v_pu_boxed_4350_; uint8_t v_t_boxed_4351_; lean_object* v_res_4352_; 
v_pu_boxed_4350_ = lean_unbox(v_pu_4341_);
v_t_boxed_4351_ = lean_unbox(v_t_4342_);
v_res_4352_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4350_, v_t_boxed_4351_, v_code_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
lean_dec_ref(v_a_4344_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4353_, uint8_t v_t_4354_, uint8_t v_pu_4355_, uint8_t v_t_4356_, lean_object* v_decl_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4355_, v_t_4356_, v_decl_4357_, v___y_4358_, v___y_4360_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4365_, lean_object* v_t_4366_, lean_object* v_pu_4367_, lean_object* v_t_4368_, lean_object* v_decl_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
uint8_t v_pu_boxed_4376_; uint8_t v_t_boxed_4377_; uint8_t v_pu_boxed_4378_; uint8_t v_t_boxed_4379_; lean_object* v_res_4380_; 
v_pu_boxed_4376_ = lean_unbox(v_pu_4365_);
v_t_boxed_4377_ = lean_unbox(v_t_4366_);
v_pu_boxed_4378_ = lean_unbox(v_pu_4367_);
v_t_boxed_4379_ = lean_unbox(v_t_4368_);
v_res_4380_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4376_, v_t_boxed_4377_, v_pu_boxed_4378_, v_t_boxed_4379_, v_decl_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec_ref(v___y_4370_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4381_, uint8_t v_t_4382_, uint8_t v_pu_4383_, uint8_t v_t_4384_, lean_object* v_args_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4383_, v_t_4384_, v_args_4385_, v___y_4386_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4393_, lean_object* v_t_4394_, lean_object* v_pu_4395_, lean_object* v_t_4396_, lean_object* v_args_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
uint8_t v_pu_boxed_4404_; uint8_t v_t_boxed_4405_; uint8_t v_pu_boxed_4406_; uint8_t v_t_boxed_4407_; lean_object* v_res_4408_; 
v_pu_boxed_4404_ = lean_unbox(v_pu_4393_);
v_t_boxed_4405_ = lean_unbox(v_t_4394_);
v_pu_boxed_4406_ = lean_unbox(v_pu_4395_);
v_t_boxed_4407_ = lean_unbox(v_t_4396_);
v_res_4408_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4404_, v_t_boxed_4405_, v_pu_boxed_4406_, v_t_boxed_4407_, v_args_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec_ref(v___y_4398_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4409_, uint8_t v_t_4410_, uint8_t v_pu_4411_, uint8_t v_t_4412_, lean_object* v_ps_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4411_, v_t_4412_, v_ps_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4421_, lean_object* v_t_4422_, lean_object* v_pu_4423_, lean_object* v_t_4424_, lean_object* v_ps_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
uint8_t v_pu_boxed_4432_; uint8_t v_t_boxed_4433_; uint8_t v_pu_boxed_4434_; uint8_t v_t_boxed_4435_; lean_object* v_res_4436_; 
v_pu_boxed_4432_ = lean_unbox(v_pu_4421_);
v_t_boxed_4433_ = lean_unbox(v_t_4422_);
v_pu_boxed_4434_ = lean_unbox(v_pu_4423_);
v_t_boxed_4435_ = lean_unbox(v_t_4424_);
v_res_4436_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4432_, v_t_boxed_4433_, v_pu_boxed_4434_, v_t_boxed_4435_, v_ps_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4437_, uint8_t v_t_4438_, lean_object* v_i_4439_, lean_object* v_as_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4437_, v_t_4438_, v_i_4439_, v_as_4440_, v___y_4441_, v___y_4443_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4448_, lean_object* v_t_4449_, lean_object* v_i_4450_, lean_object* v_as_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
uint8_t v_pu_boxed_4458_; uint8_t v_t_boxed_4459_; lean_object* v_res_4460_; 
v_pu_boxed_4458_ = lean_unbox(v_pu_4448_);
v_t_boxed_4459_ = lean_unbox(v_t_4449_);
v_res_4460_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4458_, v_t_boxed_4459_, v_i_4450_, v_as_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec_ref(v___y_4452_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4461_, uint8_t v_t_4462_, lean_object* v_decl_4463_, lean_object* v_inst_4464_, lean_object* v_____do__lift_4465_){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4466_ = lean_box(v_pu_4461_);
v___x_4467_ = lean_box(v_t_4462_);
v___x_4468_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4468_, 0, v___x_4466_);
lean_closure_set(v___x_4468_, 1, v___x_4467_);
lean_closure_set(v___x_4468_, 2, v_decl_4463_);
lean_closure_set(v___x_4468_, 3, v_____do__lift_4465_);
v___x_4469_ = lean_apply_2(v_inst_4464_, lean_box(0), v___x_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4470_, lean_object* v_t_4471_, lean_object* v_decl_4472_, lean_object* v_inst_4473_, lean_object* v_____do__lift_4474_){
_start:
{
uint8_t v_pu_boxed_4475_; uint8_t v_t_boxed_4476_; lean_object* v_res_4477_; 
v_pu_boxed_4475_ = lean_unbox(v_pu_4470_);
v_t_boxed_4476_ = lean_unbox(v_t_4471_);
v_res_4477_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4475_, v_t_boxed_4476_, v_decl_4472_, v_inst_4473_, v_____do__lift_4474_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4478_, uint8_t v_t_4479_, lean_object* v_inst_4480_, lean_object* v_inst_4481_, lean_object* v_inst_4482_, lean_object* v_decl_4483_){
_start:
{
lean_object* v_toBind_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; lean_object* v___x_4488_; 
v_toBind_4484_ = lean_ctor_get(v_inst_4481_, 1);
lean_inc(v_toBind_4484_);
lean_dec_ref(v_inst_4481_);
v___x_4485_ = lean_box(v_pu_4478_);
v___x_4486_ = lean_box(v_t_4479_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4487_, 0, v___x_4485_);
lean_closure_set(v___f_4487_, 1, v___x_4486_);
lean_closure_set(v___f_4487_, 2, v_decl_4483_);
lean_closure_set(v___f_4487_, 3, v_inst_4480_);
v___x_4488_ = lean_apply_4(v_toBind_4484_, lean_box(0), lean_box(0), v_inst_4482_, v___f_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4489_, lean_object* v_t_4490_, lean_object* v_inst_4491_, lean_object* v_inst_4492_, lean_object* v_inst_4493_, lean_object* v_decl_4494_){
_start:
{
uint8_t v_pu_boxed_4495_; uint8_t v_t_boxed_4496_; lean_object* v_res_4497_; 
v_pu_boxed_4495_ = lean_unbox(v_pu_4489_);
v_t_boxed_4496_ = lean_unbox(v_t_4490_);
v_res_4497_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4495_, v_t_boxed_4496_, v_inst_4491_, v_inst_4492_, v_inst_4493_, v_decl_4494_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4498_, uint8_t v_pu_4499_, uint8_t v_t_4500_, lean_object* v_inst_4501_, lean_object* v_inst_4502_, lean_object* v_inst_4503_, lean_object* v_decl_4504_){
_start:
{
lean_object* v_toBind_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___f_4508_; lean_object* v___x_4509_; 
v_toBind_4505_ = lean_ctor_get(v_inst_4502_, 1);
lean_inc(v_toBind_4505_);
lean_dec_ref(v_inst_4502_);
v___x_4506_ = lean_box(v_pu_4499_);
v___x_4507_ = lean_box(v_t_4500_);
v___f_4508_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4508_, 0, v___x_4506_);
lean_closure_set(v___f_4508_, 1, v___x_4507_);
lean_closure_set(v___f_4508_, 2, v_decl_4504_);
lean_closure_set(v___f_4508_, 3, v_inst_4501_);
v___x_4509_ = lean_apply_4(v_toBind_4505_, lean_box(0), lean_box(0), v_inst_4503_, v___f_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4510_, lean_object* v_pu_4511_, lean_object* v_t_4512_, lean_object* v_inst_4513_, lean_object* v_inst_4514_, lean_object* v_inst_4515_, lean_object* v_decl_4516_){
_start:
{
uint8_t v_pu_boxed_4517_; uint8_t v_t_boxed_4518_; lean_object* v_res_4519_; 
v_pu_boxed_4517_ = lean_unbox(v_pu_4511_);
v_t_boxed_4518_ = lean_unbox(v_t_4512_);
v_res_4519_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4510_, v_pu_boxed_4517_, v_t_boxed_4518_, v_inst_4513_, v_inst_4514_, v_inst_4515_, v_decl_4516_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4520_, uint8_t v_t_4521_, lean_object* v_code_4522_, lean_object* v_inst_4523_, lean_object* v_____do__lift_4524_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4525_ = lean_box(v_pu_4520_);
v___x_4526_ = lean_box(v_t_4521_);
v___x_4527_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4527_, 0, v___x_4525_);
lean_closure_set(v___x_4527_, 1, v___x_4526_);
lean_closure_set(v___x_4527_, 2, v_code_4522_);
lean_closure_set(v___x_4527_, 3, v_____do__lift_4524_);
v___x_4528_ = lean_apply_2(v_inst_4523_, lean_box(0), v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4529_, lean_object* v_t_4530_, lean_object* v_code_4531_, lean_object* v_inst_4532_, lean_object* v_____do__lift_4533_){
_start:
{
uint8_t v_pu_boxed_4534_; uint8_t v_t_boxed_4535_; lean_object* v_res_4536_; 
v_pu_boxed_4534_ = lean_unbox(v_pu_4529_);
v_t_boxed_4535_ = lean_unbox(v_t_4530_);
v_res_4536_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4534_, v_t_boxed_4535_, v_code_4531_, v_inst_4532_, v_____do__lift_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4537_, uint8_t v_t_4538_, lean_object* v_inst_4539_, lean_object* v_inst_4540_, lean_object* v_inst_4541_, lean_object* v_code_4542_){
_start:
{
lean_object* v_toBind_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___f_4546_; lean_object* v___x_4547_; 
v_toBind_4543_ = lean_ctor_get(v_inst_4540_, 1);
lean_inc(v_toBind_4543_);
lean_dec_ref(v_inst_4540_);
v___x_4544_ = lean_box(v_pu_4537_);
v___x_4545_ = lean_box(v_t_4538_);
v___f_4546_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4546_, 0, v___x_4544_);
lean_closure_set(v___f_4546_, 1, v___x_4545_);
lean_closure_set(v___f_4546_, 2, v_code_4542_);
lean_closure_set(v___f_4546_, 3, v_inst_4539_);
v___x_4547_ = lean_apply_4(v_toBind_4543_, lean_box(0), lean_box(0), v_inst_4541_, v___f_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4548_, lean_object* v_t_4549_, lean_object* v_inst_4550_, lean_object* v_inst_4551_, lean_object* v_inst_4552_, lean_object* v_code_4553_){
_start:
{
uint8_t v_pu_boxed_4554_; uint8_t v_t_boxed_4555_; lean_object* v_res_4556_; 
v_pu_boxed_4554_ = lean_unbox(v_pu_4548_);
v_t_boxed_4555_ = lean_unbox(v_t_4549_);
v_res_4556_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4554_, v_t_boxed_4555_, v_inst_4550_, v_inst_4551_, v_inst_4552_, v_code_4553_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4557_, uint8_t v_pu_4558_, uint8_t v_t_4559_, lean_object* v_inst_4560_, lean_object* v_inst_4561_, lean_object* v_inst_4562_, lean_object* v_code_4563_){
_start:
{
lean_object* v_toBind_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___f_4567_; lean_object* v___x_4568_; 
v_toBind_4564_ = lean_ctor_get(v_inst_4561_, 1);
lean_inc(v_toBind_4564_);
lean_dec_ref(v_inst_4561_);
v___x_4565_ = lean_box(v_pu_4558_);
v___x_4566_ = lean_box(v_t_4559_);
v___f_4567_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4567_, 0, v___x_4565_);
lean_closure_set(v___f_4567_, 1, v___x_4566_);
lean_closure_set(v___f_4567_, 2, v_code_4563_);
lean_closure_set(v___f_4567_, 3, v_inst_4560_);
v___x_4568_ = lean_apply_4(v_toBind_4564_, lean_box(0), lean_box(0), v_inst_4562_, v___f_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4569_, lean_object* v_pu_4570_, lean_object* v_t_4571_, lean_object* v_inst_4572_, lean_object* v_inst_4573_, lean_object* v_inst_4574_, lean_object* v_code_4575_){
_start:
{
uint8_t v_pu_boxed_4576_; uint8_t v_t_boxed_4577_; lean_object* v_res_4578_; 
v_pu_boxed_4576_ = lean_unbox(v_pu_4570_);
v_t_boxed_4577_ = lean_unbox(v_t_4571_);
v_res_4578_ = l_Lean_Compiler_LCNF_normCode(v_m_4569_, v_pu_boxed_4576_, v_t_boxed_4577_, v_inst_4572_, v_inst_4573_, v_inst_4574_, v_code_4575_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4579_, lean_object* v_e_4580_, lean_object* v_s_4581_, uint8_t v_translator_4582_){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4579_, v_s_4581_, v_translator_4582_, v_e_4580_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4586_, lean_object* v_e_4587_, lean_object* v_s_4588_, lean_object* v_translator_4589_, lean_object* v_a_4590_){
_start:
{
uint8_t v_pu_boxed_4591_; uint8_t v_translator_boxed_4592_; lean_object* v_res_4593_; 
v_pu_boxed_4591_ = lean_unbox(v_pu_4586_);
v_translator_boxed_4592_ = lean_unbox(v_translator_4589_);
v_res_4593_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4591_, v_e_4587_, v_s_4588_, v_translator_boxed_4592_);
lean_dec_ref(v_s_4588_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4594_, lean_object* v_e_4595_, lean_object* v_s_4596_, uint8_t v_translator_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v___x_4603_; 
v___x_4603_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4594_, v_e_4595_, v_s_4596_, v_translator_4597_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4604_, lean_object* v_e_4605_, lean_object* v_s_4606_, lean_object* v_translator_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
uint8_t v_pu_boxed_4613_; uint8_t v_translator_boxed_4614_; lean_object* v_res_4615_; 
v_pu_boxed_4613_ = lean_unbox(v_pu_4604_);
v_translator_boxed_4614_ = lean_unbox(v_translator_4607_);
v_res_4615_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4613_, v_e_4605_, v_s_4606_, v_translator_boxed_4614_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec_ref(v_s_4606_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4616_, lean_object* v_code_4617_, lean_object* v_s_4618_, uint8_t v_translator_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4616_, v_translator_4619_, v_code_4617_, v_s_4618_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4626_, lean_object* v_code_4627_, lean_object* v_s_4628_, lean_object* v_translator_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
uint8_t v_pu_boxed_4635_; uint8_t v_translator_boxed_4636_; lean_object* v_res_4637_; 
v_pu_boxed_4635_ = lean_unbox(v_pu_4626_);
v_translator_boxed_4636_ = lean_unbox(v_translator_4629_);
v_res_4637_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4635_, v_code_4627_, v_s_4628_, v_translator_boxed_4636_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec_ref(v_s_4628_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4641_){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4644_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4643_, v_a_4641_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4645_);
lean_dec(v_a_4645_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4649_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4660_, lean_object* v_type_4661_, uint8_t v_borrow_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v_a_4670_; lean_object* v___x_4671_; 
v___x_4668_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4669_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4668_, v_a_4664_);
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref(v___x_4669_);
v___x_4671_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4660_, v_a_4670_, v_type_4661_, v_borrow_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4672_, lean_object* v_type_4673_, lean_object* v_borrow_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
uint8_t v_pu_boxed_4680_; uint8_t v_borrow_boxed_4681_; lean_object* v_res_4682_; 
v_pu_boxed_4680_ = lean_unbox(v_pu_4672_);
v_borrow_boxed_4681_ = lean_unbox(v_borrow_4674_);
v_res_4682_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4680_, v_type_4673_, v_borrow_boxed_4681_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4683_){
_start:
{
lean_object* v_config_4685_; lean_object* v___x_4686_; 
v_config_4685_ = lean_ctor_get(v_a_4683_, 0);
lean_inc_ref(v_config_4685_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_config_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4687_);
lean_dec_ref(v_a_4687_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4690_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Compiler_LCNF_getConfig(v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4702_, lean_object* v_s_4703_, uint8_t v_phase_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4708_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4705_);
v___x_4709_ = l_Lean_Compiler_LCNF_toConfigOptions(v___x_4708_);
lean_dec_ref(v___x_4708_);
v___x_4710_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*1, v_phase_4704_);
v___x_4711_ = lean_st_mk_ref(v_s_4703_);
lean_inc(v_a_4706_);
lean_inc_ref(v_a_4705_);
lean_inc(v___x_4711_);
v___x_4712_ = lean_apply_5(v_x_4702_, v___x_4710_, v___x_4711_, v_a_4705_, v_a_4706_, lean_box(0));
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4721_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4715_ = v___x_4712_;
v_isShared_4716_ = v_isSharedCheck_4721_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4712_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4721_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4717_ = lean_st_ref_get(v___x_4711_);
lean_dec(v___x_4711_);
lean_dec(v___x_4717_);
if (v_isShared_4716_ == 0)
{
v___x_4719_ = v___x_4715_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4713_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
else
{
lean_dec(v___x_4711_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4722_, lean_object* v_s_4723_, lean_object* v_phase_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
uint8_t v_phase_boxed_4728_; lean_object* v_res_4729_; 
v_phase_boxed_4728_ = lean_unbox(v_phase_4724_);
v_res_4729_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4722_, v_s_4723_, v_phase_boxed_4728_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4730_, lean_object* v_x_4731_, lean_object* v_s_4732_, uint8_t v_phase_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4731_, v_s_4732_, v_phase_4733_, v_a_4734_, v_a_4735_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4738_, lean_object* v_x_4739_, lean_object* v_s_4740_, lean_object* v_phase_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
uint8_t v_phase_boxed_4745_; lean_object* v_res_4746_; 
v_phase_boxed_4745_ = lean_unbox(v_phase_4741_);
v_res_4746_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4738_, v_x_4739_, v_s_4740_, v_phase_boxed_4745_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
return v_res_4746_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg(){
_start:
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object* v___dummy_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4752_, lean_object* v_00_u03b2_4753_, lean_object* v_inst_4754_, lean_object* v_inst_4755_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4757_, lean_object* v_00_u03b2_4758_, lean_object* v_inst_4759_, lean_object* v_inst_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4757_, v_00_u03b2_4758_, v_inst_4759_, v_inst_4760_);
lean_dec_ref(v_inst_4760_);
lean_dec_ref(v_inst_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg(){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object* v___dummy_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
lean_dec_ref(v_a_4774_);
lean_dec_ref(v_a_4773_);
return v_res_4775_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4779_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4780_ = lean_unsigned_to_nat(14u);
v___x_4781_ = lean_unsigned_to_nat(178u);
v___x_4782_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4783_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4784_ = l_mkPanicMessageWithDecl(v___x_4783_, v___x_4782_, v___x_4781_, v___x_4780_, v___x_4779_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4785_, lean_object* v_inst_4786_, lean_object* v_snd_4787_, lean_object* v_inst_4788_, lean_object* v_s_4789_, lean_object* v_e_4790_){
_start:
{
lean_object* v_fst_4791_; lean_object* v_snd_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4807_; 
v_fst_4791_ = lean_ctor_get(v_s_4789_, 0);
v_snd_4792_ = lean_ctor_get(v_s_4789_, 1);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_s_4789_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4794_ = v_s_4789_;
v_isShared_4795_ = v_isSharedCheck_4807_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_snd_4792_);
lean_inc(v_fst_4791_);
lean_dec(v_s_4789_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4807_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4796_; lean_object* v___y_4798_; lean_object* v___x_4803_; 
lean_inc_n(v_e_4790_, 2);
v___x_4796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4796_, 0, v_e_4790_);
lean_ctor_set(v___x_4796_, 1, v_fst_4791_);
lean_inc_ref(v_inst_4786_);
lean_inc_ref(v_inst_4785_);
v___x_4803_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4785_, v_inst_4786_, v_snd_4787_, v_e_4790_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4805_ = l_panic___redArg(v_inst_4788_, v___x_4804_);
v___y_4798_ = v___x_4805_;
goto v___jp_4797_;
}
else
{
lean_object* v_val_4806_; 
v_val_4806_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_val_4806_);
lean_dec_ref_known(v___x_4803_, 1);
v___y_4798_ = v_val_4806_;
goto v___jp_4797_;
}
v___jp_4797_:
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4799_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4785_, v_inst_4786_, v_snd_4792_, v_e_4790_, v___y_4798_);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 1, v___x_4799_);
lean_ctor_set(v___x_4794_, 0, v___x_4796_);
v___x_4801_ = v___x_4794_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4796_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4808_, lean_object* v_inst_4809_, lean_object* v_snd_4810_, lean_object* v_inst_4811_, lean_object* v_s_4812_, lean_object* v_e_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4808_, v_inst_4809_, v_snd_4810_, v_inst_4811_, v_s_4812_, v_e_4813_);
lean_dec(v_inst_4811_);
lean_dec(v_snd_4810_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4815_, lean_object* v_inst_4816_, lean_object* v_inst_4817_, lean_object* v_oldState_4818_, lean_object* v_newState_4819_, lean_object* v_x_4820_, lean_object* v_s_4821_){
_start:
{
lean_object* v_fst_4822_; lean_object* v_snd_4823_; lean_object* v_fst_4824_; lean_object* v___f_4825_; lean_object* v_newEntries_4826_; lean_object* v___x_4827_; 
v_fst_4822_ = lean_ctor_get(v_newState_4819_, 0);
lean_inc(v_fst_4822_);
v_snd_4823_ = lean_ctor_get(v_newState_4819_, 1);
lean_inc(v_snd_4823_);
lean_dec_ref(v_newState_4819_);
v_fst_4824_ = lean_ctor_get(v_oldState_4818_, 0);
v___f_4825_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4825_, 0, v_inst_4815_);
lean_closure_set(v___f_4825_, 1, v_inst_4816_);
lean_closure_set(v___f_4825_, 2, v_snd_4823_);
lean_closure_set(v___f_4825_, 3, v_inst_4817_);
v_newEntries_4826_ = l_Lean_takeNewEntries___redArg(v_fst_4822_, v_fst_4824_);
v___x_4827_ = l_List_foldl___redArg(v___f_4825_, v_s_4821_, v_newEntries_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4828_, lean_object* v_inst_4829_, lean_object* v_inst_4830_, lean_object* v_oldState_4831_, lean_object* v_newState_4832_, lean_object* v_x_4833_, lean_object* v_s_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4828_, v_inst_4829_, v_inst_4830_, v_oldState_4831_, v_newState_4832_, v_x_4833_, v_s_4834_);
lean_dec(v_x_4833_);
lean_dec_ref(v_oldState_4831_);
return v_res_4835_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
return v___x_4837_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4839_ = lean_box(0);
v___x_4840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
lean_ctor_set(v___x_4840_, 1, v___x_4838_);
return v___x_4840_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4842_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4842_, 0, lean_box(0));
lean_closure_set(v___x_4842_, 1, lean_box(0));
lean_closure_set(v___x_4842_, 2, v___x_4841_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_inst_4856_){
_start:
{
lean_object* v___f_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; 
v___f_4858_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4858_, 0, v_inst_4854_);
lean_closure_set(v___f_4858_, 1, v_inst_4855_);
lean_closure_set(v___f_4858_, 2, v_inst_4856_);
v___x_4859_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___f_4858_);
v___x_4861_ = lean_box(0);
v___x_4862_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8));
v___x_4863_ = 0;
v___x_4864_ = l_Lean_registerEnvExtension___redArg(v___x_4859_, v___x_4860_, v___x_4861_, v___x_4862_, v___x_4863_, v___x_4863_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
else
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
v_a_4873_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4864_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4864_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4881_, lean_object* v_inst_4882_, lean_object* v_inst_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4881_, v_inst_4882_, v_inst_4883_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4886_, lean_object* v_00_u03b2_4887_, lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4888_, v_inst_4889_, v_inst_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4893_, lean_object* v_00_u03b2_4894_, lean_object* v_inst_4895_, lean_object* v_inst_4896_, lean_object* v_inst_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4893_, v_00_u03b2_4894_, v_inst_4895_, v_inst_4896_, v_inst_4897_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4900_, lean_object* v_inst_4901_, lean_object* v_inst_4902_, lean_object* v_b_4903_, lean_object* v_x_4904_){
_start:
{
lean_object* v_fst_4905_; lean_object* v_snd_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4915_; 
v_fst_4905_ = lean_ctor_get(v_x_4904_, 0);
v_snd_4906_ = lean_ctor_get(v_x_4904_, 1);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_x_4904_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4908_ = v_x_4904_;
v_isShared_4909_ = v_isSharedCheck_4915_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_snd_4906_);
lean_inc(v_fst_4905_);
lean_dec(v_x_4904_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4915_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4913_; 
lean_inc(v_a_4900_);
v___x_4910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4910_, 0, v_a_4900_);
lean_ctor_set(v___x_4910_, 1, v_fst_4905_);
v___x_4911_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4901_, v_inst_4902_, v_snd_4906_, v_a_4900_, v_b_4903_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v___x_4911_);
lean_ctor_set(v___x_4908_, 0, v___x_4910_);
v___x_4913_ = v___x_4908_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4911_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4916_);
return v___x_4917_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4920_, lean_object* v_inst_4921_, lean_object* v_ext_4922_, lean_object* v_a_4923_, lean_object* v_b_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v___f_4927_; lean_object* v___x_4928_; lean_object* v_env_4929_; lean_object* v_nextMacroScope_4930_; lean_object* v_ngen_4931_; lean_object* v_auxDeclNGen_4932_; lean_object* v_traceState_4933_; lean_object* v_recordedDeps_4934_; lean_object* v_messages_4935_; lean_object* v_infoState_4936_; lean_object* v_snapshotTasks_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4957_; 
v___f_4927_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4927_, 0, v_a_4923_);
lean_closure_set(v___f_4927_, 1, v_inst_4920_);
lean_closure_set(v___f_4927_, 2, v_inst_4921_);
lean_closure_set(v___f_4927_, 3, v_b_4924_);
v___x_4928_ = lean_st_ref_take(v_a_4925_);
v_env_4929_ = lean_ctor_get(v___x_4928_, 0);
v_nextMacroScope_4930_ = lean_ctor_get(v___x_4928_, 1);
v_ngen_4931_ = lean_ctor_get(v___x_4928_, 2);
v_auxDeclNGen_4932_ = lean_ctor_get(v___x_4928_, 3);
v_traceState_4933_ = lean_ctor_get(v___x_4928_, 4);
v_recordedDeps_4934_ = lean_ctor_get(v___x_4928_, 6);
v_messages_4935_ = lean_ctor_get(v___x_4928_, 7);
v_infoState_4936_ = lean_ctor_get(v___x_4928_, 8);
v_snapshotTasks_4937_ = lean_ctor_get(v___x_4928_, 9);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v___x_4928_, 5);
lean_dec(v_unused_4958_);
v___x_4939_ = v___x_4928_;
v_isShared_4940_ = v_isSharedCheck_4957_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_snapshotTasks_4937_);
lean_inc(v_infoState_4936_);
lean_inc(v_messages_4935_);
lean_inc(v_recordedDeps_4934_);
lean_inc(v_traceState_4933_);
lean_inc(v_auxDeclNGen_4932_);
lean_inc(v_ngen_4931_);
lean_inc(v_nextMacroScope_4930_);
lean_inc(v_env_4929_);
lean_dec(v___x_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4957_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_asyncMode_4941_; uint8_t v_logWrites_4942_; lean_object* v___x_4943_; lean_object* v___y_4945_; lean_object* v___x_4952_; uint8_t v___x_4953_; 
v_asyncMode_4941_ = lean_ctor_get(v_ext_4922_, 2);
lean_inc(v_asyncMode_4941_);
v_logWrites_4942_ = lean_ctor_get_uint8(v_ext_4922_, sizeof(void*)*6);
v___x_4943_ = lean_box(0);
v___x_4952_ = lean_box(0);
v___x_4953_ = 1;
if (v_logWrites_4942_ == 0)
{
lean_object* v___x_4954_; 
v___x_4954_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_4922_, v_env_4929_, v___f_4927_, v_asyncMode_4941_, v___x_4952_, v___x_4953_);
lean_dec(v_asyncMode_4941_);
v___y_4945_ = v___x_4954_;
goto v___jp_4944_;
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_inc_ref(v_ext_4922_);
v___x_4955_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_ext_4922_, v_env_4929_);
lean_dec_ref(v_env_4929_);
v___x_4956_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_4922_, v___x_4955_, v___f_4927_, v_asyncMode_4941_, v___x_4952_, v___x_4953_);
lean_dec(v_asyncMode_4941_);
v___y_4945_ = v___x_4956_;
goto v___jp_4944_;
}
v___jp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4946_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 5, v___x_4946_);
lean_ctor_set(v___x_4939_, 0, v___y_4945_);
v___x_4948_ = v___x_4939_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___y_4945_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4930_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4931_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4932_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v_traceState_4933_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_recordedDeps_4934_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_messages_4935_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_infoState_4936_);
lean_ctor_set(v_reuseFailAlloc_4951_, 9, v_snapshotTasks_4937_);
v___x_4948_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_st_ref_put(v_a_4925_, v___x_4948_);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4943_);
return v___x_4950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4959_, lean_object* v_inst_4960_, lean_object* v_ext_4961_, lean_object* v_a_4962_, lean_object* v_b_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4959_, v_inst_4960_, v_ext_4961_, v_a_4962_, v_b_4963_, v_a_4964_);
lean_dec(v_a_4964_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4967_, lean_object* v_00_u03b2_4968_, lean_object* v_inst_4969_, lean_object* v_inst_4970_, lean_object* v_inst_4971_, lean_object* v_ext_4972_, lean_object* v_a_4973_, lean_object* v_b_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v___x_4978_; 
v___x_4978_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4969_, v_inst_4970_, v_ext_4972_, v_a_4973_, v_b_4974_, v_a_4976_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4979_, lean_object* v_00_u03b2_4980_, lean_object* v_inst_4981_, lean_object* v_inst_4982_, lean_object* v_inst_4983_, lean_object* v_ext_4984_, lean_object* v_a_4985_, lean_object* v_b_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4979_, v_00_u03b2_4980_, v_inst_4981_, v_inst_4982_, v_inst_4983_, v_ext_4984_, v_a_4985_, v_b_4986_, v_a_4987_, v_a_4988_);
lean_dec(v_a_4988_);
lean_dec_ref(v_a_4987_);
lean_dec(v_inst_4983_);
return v_res_4990_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_4991_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0);
v___x_4993_ = lean_box(0);
v___x_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
lean_ctor_set(v___x_4994_, 1, v___x_4992_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4995_, lean_object* v_inst_4996_, lean_object* v_ext_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v_env_5003_; lean_object* v_asyncMode_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; lean_object* v___x_5007_; lean_object* v_snd_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5001_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1);
v___x_5002_ = lean_st_ref_get(v_a_4999_);
v_env_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc_ref(v_env_5003_);
lean_dec(v___x_5002_);
v_asyncMode_5004_ = lean_ctor_get(v_ext_4997_, 2);
v___x_5005_ = lean_box(0);
v___x_5006_ = 0;
v___x_5007_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5001_, v_ext_4997_, v_env_5003_, v_asyncMode_5004_, v___x_5005_, v___x_5006_);
v_snd_5008_ = lean_ctor_get(v___x_5007_, 1);
lean_inc(v_snd_5008_);
lean_dec(v___x_5007_);
v___x_5009_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4995_, v_inst_4996_, v_snd_5008_, v_a_4998_);
lean_dec(v_snd_5008_);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_5011_, lean_object* v_inst_5012_, lean_object* v_ext_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5011_, v_inst_5012_, v_ext_5013_, v_a_5014_, v_a_5015_);
lean_dec(v_a_5015_);
lean_dec_ref(v_ext_5013_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_5018_, lean_object* v_00_u03b2_5019_, lean_object* v_inst_5020_, lean_object* v_inst_5021_, lean_object* v_inst_5022_, lean_object* v_ext_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5020_, v_inst_5021_, v_ext_5023_, v_a_5024_, v_a_5026_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5029_, lean_object* v_00_u03b2_5030_, lean_object* v_inst_5031_, lean_object* v_inst_5032_, lean_object* v_inst_5033_, lean_object* v_ext_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5029_, v_00_u03b2_5030_, v_inst_5031_, v_inst_5032_, v_inst_5033_, v_ext_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
lean_dec(v_a_5037_);
lean_dec_ref(v_a_5036_);
lean_dec_ref(v_ext_5034_);
lean_dec(v_inst_5033_);
return v_res_5039_;
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
