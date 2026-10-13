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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t v___x_1354_; 
v___x_1354_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1354_ == 0)
{
if (v___x_1352_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1351_);
return v___x_1355_;
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_of_nat(v___x_1350_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1342_, v_decls_1343_, v___x_1356_, v___x_1357_, v___x_1351_, v_a_1345_);
return v___x_1358_;
}
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1350_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1342_, v_decls_1343_, v___x_1359_, v___x_1360_, v___x_1351_, v_a_1345_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1362_, lean_object* v_decls_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
uint8_t v_pu_boxed_1369_; lean_object* v_res_1370_; 
v_pu_boxed_1369_ = lean_unbox(v_pu_1362_);
v_res_1370_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1369_, v_decls_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_decls_1363_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1371_, lean_object* v_as_1372_, size_t v_i_1373_, size_t v_stop_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1371_, v_as_1372_, v_i_1373_, v_stop_1374_, v_b_1375_, v___y_1377_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1382_, lean_object* v_as_1383_, lean_object* v_i_1384_, lean_object* v_stop_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_pu_boxed_1392_; size_t v_i_boxed_1393_; size_t v_stop_boxed_1394_; lean_object* v_res_1395_; 
v_pu_boxed_1392_ = lean_unbox(v_pu_1382_);
v_i_boxed_1393_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_stop_boxed_1394_ = lean_unbox_usize(v_stop_1385_);
lean_dec(v_stop_1385_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1392_, v_as_1383_, v_i_boxed_1393_, v_stop_boxed_1394_, v_b_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec_ref(v_as_1383_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1396_, lean_object* v_v_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
if (lean_obj_tag(v_v_1397_) == 0)
{
lean_object* v_code_1403_; lean_object* v___x_1404_; 
v_code_1403_ = lean_ctor_get(v_v_1397_, 0);
lean_inc_ref(v_code_1403_);
lean_dec_ref_known(v_v_1397_, 1);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
v___x_1404_ = lean_apply_6(v_f_1396_, v_code_1403_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, lean_box(0));
return v___x_1404_;
}
else
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_f_1396_);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_v_1397_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_v_1397_, 0);
lean_dec(v_unused_1413_);
v___x_1406_ = v_v_1397_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_v_1397_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_box(0);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1414_, lean_object* v_v_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1414_, v_v_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1422_, lean_object* v_f_1423_, lean_object* v_v_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1423_, v_v_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1431_, lean_object* v_f_1432_, lean_object* v_v_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v_pu_boxed_1439_; lean_object* v_res_1440_; 
v_pu_boxed_1439_ = lean_unbox(v_pu_1431_);
v_res_1440_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1439_, v_f_1432_, v_v_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1441_, lean_object* v_decl_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_toSignature_1448_; lean_object* v_value_1449_; lean_object* v_params_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_toSignature_1448_ = lean_ctor_get(v_decl_1442_, 0);
lean_inc_ref(v_toSignature_1448_);
v_value_1449_ = lean_ctor_get(v_decl_1442_, 1);
lean_inc_ref(v_value_1449_);
lean_dec_ref(v_decl_1442_);
v_params_1450_ = lean_ctor_get(v_toSignature_1448_, 3);
lean_inc_ref(v_params_1450_);
lean_dec_ref(v_toSignature_1448_);
v___x_1451_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1441_, v_params_1450_, v_a_1444_);
lean_dec_ref(v_params_1450_);
lean_dec_ref(v___x_1451_);
v___x_1452_ = lean_box(v_pu_1441_);
v___x_1453_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1453_, 0, v___x_1452_);
v___x_1454_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1453_, v_value_1449_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1455_, lean_object* v_decl_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
uint8_t v_pu_boxed_1462_; lean_object* v_res_1463_; 
v_pu_boxed_1462_ = lean_unbox(v_pu_1455_);
v_res_1463_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1462_, v_decl_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1464_, lean_object* v_decl_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1464_, v_decl_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1472_, lean_object* v_decl_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
uint8_t v_pu_boxed_1479_; lean_object* v_res_1480_; 
v_pu_boxed_1479_ = lean_unbox(v_pu_1472_);
v_res_1480_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1479_, v_decl_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = l_Lean_instInhabitedExpr;
v___x_1483_ = lean_panic_fn_borrowed(v___x_1482_, v_msg_1481_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1488_ = lean_unsigned_to_nat(20u);
v___x_1489_ = lean_unsigned_to_nat(215u);
v___x_1490_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1491_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1492_ = l_mkPanicMessageWithDecl(v___x_1491_, v___x_1490_, v___x_1489_, v___x_1488_, v___x_1487_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1493_, lean_object* v_s_1494_, uint8_t v_translator_1495_, lean_object* v_e_1496_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_Expr_hasFVar(v_e_1496_);
if (v___x_1497_ == 0)
{
return v_e_1496_;
}
else
{
switch(lean_obj_tag(v_e_1496_))
{
case 1:
{
lean_object* v_fvarId_1498_; lean_object* v___x_1499_; 
v_fvarId_1498_ = lean_ctor_get(v_e_1496_, 0);
v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1494_, v_fvarId_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
return v_e_1496_;
}
else
{
lean_object* v_val_1500_; 
lean_dec_ref_known(v_e_1496_, 1);
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
switch(lean_obj_tag(v_val_1500_))
{
case 0:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1501_;
}
case 1:
{
if (v_translator_1495_ == 0)
{
lean_object* v_fvarId_1502_; lean_object* v___x_1503_; 
v_fvarId_1502_ = lean_ctor_get(v_val_1500_, 0);
lean_inc(v_fvarId_1502_);
lean_dec_ref_known(v_val_1500_, 1);
v___x_1503_ = l_Lean_Expr_fvar___override(v_fvarId_1502_);
v_e_1496_ = v___x_1503_;
goto _start;
}
else
{
lean_object* v_fvarId_1505_; lean_object* v___x_1506_; 
v_fvarId_1505_ = lean_ctor_get(v_val_1500_, 0);
lean_inc(v_fvarId_1505_);
lean_dec_ref_known(v_val_1500_, 1);
v___x_1506_ = l_Lean_Expr_fvar___override(v_fvarId_1505_);
return v___x_1506_;
}
}
default: 
{
if (v_translator_1495_ == 0)
{
lean_object* v_expr_1507_; 
v_expr_1507_ = lean_ctor_get(v_val_1500_, 0);
lean_inc_ref(v_expr_1507_);
lean_dec_ref_known(v_val_1500_, 1);
v_e_1496_ = v_expr_1507_;
goto _start;
}
else
{
lean_object* v_expr_1509_; 
v_expr_1509_ = lean_ctor_get(v_val_1500_, 0);
lean_inc_ref(v_expr_1509_);
lean_dec_ref_known(v_val_1500_, 1);
return v_expr_1509_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1510_; lean_object* v_arg_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; uint8_t v___x_1516_; 
v_fn_1510_ = lean_ctor_get(v_e_1496_, 0);
v_arg_1511_ = lean_ctor_get(v_e_1496_, 1);
lean_inc_ref(v_fn_1510_);
v___x_1512_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1493_, v_s_1494_, v_translator_1495_, v_fn_1510_);
lean_inc_ref(v_arg_1511_);
v___x_1513_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_arg_1511_);
v___x_1514_ = lean_ptr_addr(v_fn_1510_);
v___x_1515_ = lean_ptr_addr(v___x_1512_);
v___x_1516_ = lean_usize_dec_eq(v___x_1514_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref_known(v_e_1496_, 2);
v___x_1517_ = l_Lean_Expr_app___override(v___x_1512_, v___x_1513_);
v___x_1518_ = l_Lean_Expr_headBeta(v___x_1517_);
return v___x_1518_;
}
else
{
size_t v___x_1519_; size_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = lean_ptr_addr(v_arg_1511_);
v___x_1520_ = lean_ptr_addr(v___x_1513_);
v___x_1521_ = lean_usize_dec_eq(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_dec_ref_known(v_e_1496_, 2);
v___x_1522_ = l_Lean_Expr_app___override(v___x_1512_, v___x_1513_);
v___x_1523_ = l_Lean_Expr_headBeta(v___x_1522_);
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; 
lean_dec_ref(v___x_1513_);
lean_dec_ref(v___x_1512_);
v___x_1524_ = l_Lean_Expr_headBeta(v_e_1496_);
return v___x_1524_;
}
}
}
case 6:
{
lean_object* v_binderName_1525_; lean_object* v_binderType_1526_; lean_object* v_body_1527_; uint8_t v_binderInfo_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; uint8_t v___x_1533_; 
v_binderName_1525_ = lean_ctor_get(v_e_1496_, 0);
v_binderType_1526_ = lean_ctor_get(v_e_1496_, 1);
v_body_1527_ = lean_ctor_get(v_e_1496_, 2);
v_binderInfo_1528_ = lean_ctor_get_uint8(v_e_1496_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1526_);
v___x_1529_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_binderType_1526_);
lean_inc_ref(v_body_1527_);
v___x_1530_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_body_1527_);
v___x_1531_ = lean_ptr_addr(v_binderType_1526_);
v___x_1532_ = lean_ptr_addr(v___x_1529_);
v___x_1533_ = lean_usize_dec_eq(v___x_1531_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_inc(v_binderName_1525_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1534_ = l_Lean_Expr_lam___override(v_binderName_1525_, v___x_1529_, v___x_1530_, v_binderInfo_1528_);
return v___x_1534_;
}
else
{
size_t v___x_1535_; size_t v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_ptr_addr(v_body_1527_);
v___x_1536_ = lean_ptr_addr(v___x_1530_);
v___x_1537_ = lean_usize_dec_eq(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_inc(v_binderName_1525_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1538_ = l_Lean_Expr_lam___override(v_binderName_1525_, v___x_1529_, v___x_1530_, v_binderInfo_1528_);
return v___x_1538_;
}
else
{
uint8_t v___x_1539_; 
v___x_1539_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1528_, v_binderInfo_1528_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_inc(v_binderName_1525_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1540_ = l_Lean_Expr_lam___override(v_binderName_1525_, v___x_1529_, v___x_1530_, v_binderInfo_1528_);
return v___x_1540_;
}
else
{
lean_dec_ref(v___x_1530_);
lean_dec_ref(v___x_1529_);
return v_e_1496_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1541_; lean_object* v_binderType_1542_; lean_object* v_body_1543_; uint8_t v_binderInfo_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v_binderName_1541_ = lean_ctor_get(v_e_1496_, 0);
v_binderType_1542_ = lean_ctor_get(v_e_1496_, 1);
v_body_1543_ = lean_ctor_get(v_e_1496_, 2);
v_binderInfo_1544_ = lean_ctor_get_uint8(v_e_1496_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1542_);
v___x_1545_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_binderType_1542_);
lean_inc_ref(v_body_1543_);
v___x_1546_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_body_1543_);
v___x_1547_ = lean_ptr_addr(v_binderType_1542_);
v___x_1548_ = lean_ptr_addr(v___x_1545_);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_inc(v_binderName_1541_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1550_ = l_Lean_Expr_forallE___override(v_binderName_1541_, v___x_1545_, v___x_1546_, v_binderInfo_1544_);
return v___x_1550_;
}
else
{
size_t v___x_1551_; size_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1551_ = lean_ptr_addr(v_body_1543_);
v___x_1552_ = lean_ptr_addr(v___x_1546_);
v___x_1553_ = lean_usize_dec_eq(v___x_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_inc(v_binderName_1541_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1554_ = l_Lean_Expr_forallE___override(v_binderName_1541_, v___x_1545_, v___x_1546_, v_binderInfo_1544_);
return v___x_1554_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1544_, v_binderInfo_1544_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_inc(v_binderName_1541_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1556_ = l_Lean_Expr_forallE___override(v_binderName_1541_, v___x_1545_, v___x_1546_, v_binderInfo_1544_);
return v___x_1556_;
}
else
{
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
return v_e_1496_;
}
}
}
}
case 8:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref_known(v_e_1496_, 4);
v___x_1557_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1558_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1557_);
return v___x_1558_;
}
case 10:
{
lean_object* v_data_1559_; lean_object* v_expr_1560_; lean_object* v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; uint8_t v___x_1564_; 
v_data_1559_ = lean_ctor_get(v_e_1496_, 0);
v_expr_1560_ = lean_ctor_get(v_e_1496_, 1);
lean_inc_ref(v_expr_1560_);
v___x_1561_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_expr_1560_);
v___x_1562_ = lean_ptr_addr(v_expr_1560_);
v___x_1563_ = lean_ptr_addr(v___x_1561_);
v___x_1564_ = lean_usize_dec_eq(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
lean_inc(v_data_1559_);
lean_dec_ref_known(v_e_1496_, 2);
v___x_1565_ = l_Lean_Expr_mdata___override(v_data_1559_, v___x_1561_);
return v___x_1565_;
}
else
{
lean_dec_ref(v___x_1561_);
return v_e_1496_;
}
}
case 11:
{
lean_object* v_typeName_1566_; lean_object* v_idx_1567_; lean_object* v_struct_1568_; lean_object* v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; uint8_t v___x_1572_; 
v_typeName_1566_ = lean_ctor_get(v_e_1496_, 0);
v_idx_1567_ = lean_ctor_get(v_e_1496_, 1);
v_struct_1568_ = lean_ctor_get(v_e_1496_, 2);
lean_inc_ref(v_struct_1568_);
v___x_1569_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1493_, v_s_1494_, v_translator_1495_, v_struct_1568_);
v___x_1570_ = lean_ptr_addr(v_struct_1568_);
v___x_1571_ = lean_ptr_addr(v___x_1569_);
v___x_1572_ = lean_usize_dec_eq(v___x_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; 
lean_inc(v_idx_1567_);
lean_inc(v_typeName_1566_);
lean_dec_ref_known(v_e_1496_, 3);
v___x_1573_ = l_Lean_Expr_proj___override(v_typeName_1566_, v_idx_1567_, v___x_1569_);
return v___x_1573_;
}
else
{
lean_dec_ref(v___x_1569_);
return v_e_1496_;
}
}
default: 
{
return v_e_1496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1574_, lean_object* v_s_1575_, uint8_t v_translator_1576_, lean_object* v_e_1577_){
_start:
{
if (lean_obj_tag(v_e_1577_) == 5)
{
lean_object* v_fn_1578_; lean_object* v_arg_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; uint8_t v___x_1584_; 
v_fn_1578_ = lean_ctor_get(v_e_1577_, 0);
v_arg_1579_ = lean_ctor_get(v_e_1577_, 1);
lean_inc_ref(v_fn_1578_);
v___x_1580_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1574_, v_s_1575_, v_translator_1576_, v_fn_1578_);
lean_inc_ref(v_arg_1579_);
v___x_1581_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1574_, v_s_1575_, v_translator_1576_, v_arg_1579_);
v___x_1582_ = lean_ptr_addr(v_fn_1578_);
v___x_1583_ = lean_ptr_addr(v___x_1580_);
v___x_1584_ = lean_usize_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref_known(v_e_1577_, 2);
v___x_1585_ = l_Lean_Expr_app___override(v___x_1580_, v___x_1581_);
return v___x_1585_;
}
else
{
size_t v___x_1586_; size_t v___x_1587_; uint8_t v___x_1588_; 
v___x_1586_ = lean_ptr_addr(v_arg_1579_);
v___x_1587_ = lean_ptr_addr(v___x_1581_);
v___x_1588_ = lean_usize_dec_eq(v___x_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
lean_dec_ref_known(v_e_1577_, 2);
v___x_1589_ = l_Lean_Expr_app___override(v___x_1580_, v___x_1581_);
return v___x_1589_;
}
else
{
lean_dec_ref(v___x_1581_);
lean_dec_ref(v___x_1580_);
return v_e_1577_;
}
}
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1574_, v_s_1575_, v_translator_1576_, v_e_1577_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1591_, lean_object* v_s_1592_, lean_object* v_translator_1593_, lean_object* v_e_1594_){
_start:
{
uint8_t v_pu_boxed_1595_; uint8_t v_translator_boxed_1596_; lean_object* v_res_1597_; 
v_pu_boxed_1595_ = lean_unbox(v_pu_1591_);
v_translator_boxed_1596_ = lean_unbox(v_translator_1593_);
v_res_1597_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1595_, v_s_1592_, v_translator_boxed_1596_, v_e_1594_);
lean_dec_ref(v_s_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1598_, lean_object* v_s_1599_, lean_object* v_translator_1600_, lean_object* v_e_1601_){
_start:
{
uint8_t v_pu_boxed_1602_; uint8_t v_translator_boxed_1603_; lean_object* v_res_1604_; 
v_pu_boxed_1602_ = lean_unbox(v_pu_1598_);
v_translator_boxed_1603_ = lean_unbox(v_translator_1600_);
v_res_1604_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1602_, v_s_1599_, v_translator_boxed_1603_, v_e_1601_);
lean_dec_ref(v_s_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1605_, lean_object* v_s_1606_, lean_object* v_e_1607_, uint8_t v_translator_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1605_, v_s_1606_, v_translator_1608_, v_e_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1610_, lean_object* v_s_1611_, lean_object* v_e_1612_, lean_object* v_translator_1613_){
_start:
{
uint8_t v_pu_boxed_1614_; uint8_t v_translator_boxed_1615_; lean_object* v_res_1616_; 
v_pu_boxed_1614_ = lean_unbox(v_pu_1610_);
v_translator_boxed_1615_ = lean_unbox(v_translator_1613_);
v_res_1616_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1614_, v_s_1611_, v_e_1612_, v_translator_boxed_1615_);
lean_dec_ref(v_s_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(lean_object* v_x_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_tag_nat(v_x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl___boxed(lean_object* v_x_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(v_x_1619_);
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
lean_dec_ref(v_ty_1822_);
lean_dec_ref_known(v_e_1768_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_inst_4850_){
_start:
{
lean_object* v___f_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; uint8_t v___x_4857_; lean_object* v___x_4858_; 
v___f_4852_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4852_, 0, v_inst_4848_);
lean_closure_set(v___f_4852_, 1, v_inst_4849_);
lean_closure_set(v___f_4852_, 2, v_inst_4850_);
v___x_4853_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___f_4852_);
v___x_4855_ = lean_box(0);
v___x_4856_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8));
v___x_4857_ = 0;
v___x_4858_ = l_Lean_registerEnvExtension___redArg(v___x_4853_, v___x_4854_, v___x_4855_, v___x_4856_, v___x_4857_, v___x_4857_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4858_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4858_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
v_a_4867_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4858_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4858_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4875_, lean_object* v_inst_4876_, lean_object* v_inst_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4875_, v_inst_4876_, v_inst_4877_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4880_, lean_object* v_00_u03b2_4881_, lean_object* v_inst_4882_, lean_object* v_inst_4883_, lean_object* v_inst_4884_){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4882_, v_inst_4883_, v_inst_4884_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4887_, lean_object* v_00_u03b2_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_inst_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4887_, v_00_u03b2_4888_, v_inst_4889_, v_inst_4890_, v_inst_4891_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4894_, lean_object* v_inst_4895_, lean_object* v_inst_4896_, lean_object* v_b_4897_, lean_object* v_x_4898_){
_start:
{
lean_object* v_fst_4899_; lean_object* v_snd_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4909_; 
v_fst_4899_ = lean_ctor_get(v_x_4898_, 0);
v_snd_4900_ = lean_ctor_get(v_x_4898_, 1);
v_isSharedCheck_4909_ = !lean_is_exclusive(v_x_4898_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4902_ = v_x_4898_;
v_isShared_4903_ = v_isSharedCheck_4909_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_snd_4900_);
lean_inc(v_fst_4899_);
lean_dec(v_x_4898_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4909_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4907_; 
lean_inc(v_a_4894_);
v___x_4904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_a_4894_);
lean_ctor_set(v___x_4904_, 1, v_fst_4899_);
v___x_4905_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4895_, v_inst_4896_, v_snd_4900_, v_a_4894_, v_b_4897_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 1, v___x_4905_);
lean_ctor_set(v___x_4902_, 0, v___x_4904_);
v___x_4907_ = v___x_4902_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
return v___x_4911_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
lean_ctor_set(v___x_4913_, 1, v___x_4912_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4914_, lean_object* v_inst_4915_, lean_object* v_ext_4916_, lean_object* v_a_4917_, lean_object* v_b_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v___f_4921_; lean_object* v___x_4922_; lean_object* v_env_4923_; lean_object* v_nextMacroScope_4924_; lean_object* v_ngen_4925_; lean_object* v_auxDeclNGen_4926_; lean_object* v_traceState_4927_; lean_object* v_recordedDeps_4928_; lean_object* v_messages_4929_; lean_object* v_infoState_4930_; lean_object* v_snapshotTasks_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4951_; 
v___f_4921_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4921_, 0, v_a_4917_);
lean_closure_set(v___f_4921_, 1, v_inst_4914_);
lean_closure_set(v___f_4921_, 2, v_inst_4915_);
lean_closure_set(v___f_4921_, 3, v_b_4918_);
v___x_4922_ = lean_st_ref_take(v_a_4919_);
v_env_4923_ = lean_ctor_get(v___x_4922_, 0);
v_nextMacroScope_4924_ = lean_ctor_get(v___x_4922_, 1);
v_ngen_4925_ = lean_ctor_get(v___x_4922_, 2);
v_auxDeclNGen_4926_ = lean_ctor_get(v___x_4922_, 3);
v_traceState_4927_ = lean_ctor_get(v___x_4922_, 4);
v_recordedDeps_4928_ = lean_ctor_get(v___x_4922_, 6);
v_messages_4929_ = lean_ctor_get(v___x_4922_, 7);
v_infoState_4930_ = lean_ctor_get(v___x_4922_, 8);
v_snapshotTasks_4931_ = lean_ctor_get(v___x_4922_, 9);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4951_ == 0)
{
lean_object* v_unused_4952_; 
v_unused_4952_ = lean_ctor_get(v___x_4922_, 5);
lean_dec(v_unused_4952_);
v___x_4933_ = v___x_4922_;
v_isShared_4934_ = v_isSharedCheck_4951_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_snapshotTasks_4931_);
lean_inc(v_infoState_4930_);
lean_inc(v_messages_4929_);
lean_inc(v_recordedDeps_4928_);
lean_inc(v_traceState_4927_);
lean_inc(v_auxDeclNGen_4926_);
lean_inc(v_ngen_4925_);
lean_inc(v_nextMacroScope_4924_);
lean_inc(v_env_4923_);
lean_dec(v___x_4922_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4951_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v_asyncMode_4935_; uint8_t v_logWrites_4936_; lean_object* v___x_4937_; lean_object* v___y_4939_; lean_object* v___x_4946_; uint8_t v___x_4947_; 
v_asyncMode_4935_ = lean_ctor_get(v_ext_4916_, 2);
lean_inc(v_asyncMode_4935_);
v_logWrites_4936_ = lean_ctor_get_uint8(v_ext_4916_, sizeof(void*)*6);
v___x_4937_ = lean_box(0);
v___x_4946_ = lean_box(0);
v___x_4947_ = 1;
if (v_logWrites_4936_ == 0)
{
lean_object* v___x_4948_; 
v___x_4948_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_4916_, v_env_4923_, v___f_4921_, v_asyncMode_4935_, v___x_4946_, v___x_4947_);
lean_dec(v_asyncMode_4935_);
v___y_4939_ = v___x_4948_;
goto v___jp_4938_;
}
else
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
lean_inc_ref(v_ext_4916_);
v___x_4949_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_ext_4916_, v_env_4923_);
lean_dec_ref(v_env_4923_);
v___x_4950_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_4916_, v___x_4949_, v___f_4921_, v_asyncMode_4935_, v___x_4946_, v___x_4947_);
lean_dec(v_asyncMode_4935_);
v___y_4939_ = v___x_4950_;
goto v___jp_4938_;
}
v___jp_4938_:
{
lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4940_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 5, v___x_4940_);
lean_ctor_set(v___x_4933_, 0, v___y_4939_);
v___x_4942_ = v___x_4933_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v___y_4939_);
lean_ctor_set(v_reuseFailAlloc_4945_, 1, v_nextMacroScope_4924_);
lean_ctor_set(v_reuseFailAlloc_4945_, 2, v_ngen_4925_);
lean_ctor_set(v_reuseFailAlloc_4945_, 3, v_auxDeclNGen_4926_);
lean_ctor_set(v_reuseFailAlloc_4945_, 4, v_traceState_4927_);
lean_ctor_set(v_reuseFailAlloc_4945_, 5, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_4945_, 6, v_recordedDeps_4928_);
lean_ctor_set(v_reuseFailAlloc_4945_, 7, v_messages_4929_);
lean_ctor_set(v_reuseFailAlloc_4945_, 8, v_infoState_4930_);
lean_ctor_set(v_reuseFailAlloc_4945_, 9, v_snapshotTasks_4931_);
v___x_4942_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4943_ = lean_st_ref_put(v_a_4919_, v___x_4942_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4937_);
return v___x_4944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4953_, lean_object* v_inst_4954_, lean_object* v_ext_4955_, lean_object* v_a_4956_, lean_object* v_b_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4953_, v_inst_4954_, v_ext_4955_, v_a_4956_, v_b_4957_, v_a_4958_);
lean_dec(v_a_4958_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4961_, lean_object* v_00_u03b2_4962_, lean_object* v_inst_4963_, lean_object* v_inst_4964_, lean_object* v_inst_4965_, lean_object* v_ext_4966_, lean_object* v_a_4967_, lean_object* v_b_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4963_, v_inst_4964_, v_ext_4966_, v_a_4967_, v_b_4968_, v_a_4970_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4973_, lean_object* v_00_u03b2_4974_, lean_object* v_inst_4975_, lean_object* v_inst_4976_, lean_object* v_inst_4977_, lean_object* v_ext_4978_, lean_object* v_a_4979_, lean_object* v_b_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4973_, v_00_u03b2_4974_, v_inst_4975_, v_inst_4976_, v_inst_4977_, v_ext_4978_, v_a_4979_, v_b_4980_, v_a_4981_, v_a_4982_);
lean_dec(v_a_4982_);
lean_dec_ref(v_a_4981_);
lean_dec(v_inst_4977_);
return v_res_4984_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_4985_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4986_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0);
v___x_4987_ = lean_box(0);
v___x_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
lean_ctor_set(v___x_4988_, 1, v___x_4986_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4989_, lean_object* v_inst_4990_, lean_object* v_ext_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v_env_4997_; lean_object* v_asyncMode_4998_; lean_object* v___x_4999_; uint8_t v___x_5000_; lean_object* v___x_5001_; lean_object* v_snd_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_4995_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1);
v___x_4996_ = lean_st_ref_get(v_a_4993_);
v_env_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc_ref(v_env_4997_);
lean_dec(v___x_4996_);
v_asyncMode_4998_ = lean_ctor_get(v_ext_4991_, 2);
v___x_4999_ = lean_box(0);
v___x_5000_ = 0;
v___x_5001_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4995_, v_ext_4991_, v_env_4997_, v_asyncMode_4998_, v___x_4999_, v___x_5000_);
v_snd_5002_ = lean_ctor_get(v___x_5001_, 1);
lean_inc(v_snd_5002_);
lean_dec(v___x_5001_);
v___x_5003_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4989_, v_inst_4990_, v_snd_5002_, v_a_4992_);
lean_dec(v_snd_5002_);
v___x_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_5005_, lean_object* v_inst_5006_, lean_object* v_ext_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5005_, v_inst_5006_, v_ext_5007_, v_a_5008_, v_a_5009_);
lean_dec(v_a_5009_);
lean_dec_ref(v_ext_5007_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_5012_, lean_object* v_00_u03b2_5013_, lean_object* v_inst_5014_, lean_object* v_inst_5015_, lean_object* v_inst_5016_, lean_object* v_ext_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5014_, v_inst_5015_, v_ext_5017_, v_a_5018_, v_a_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5023_, lean_object* v_00_u03b2_5024_, lean_object* v_inst_5025_, lean_object* v_inst_5026_, lean_object* v_inst_5027_, lean_object* v_ext_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5023_, v_00_u03b2_5024_, v_inst_5025_, v_inst_5026_, v_inst_5027_, v_ext_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
lean_dec_ref(v_ext_5028_);
lean_dec(v_inst_5027_);
return v_res_5033_;
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
