// Lean compiler output
// Module: Lean.Compiler.LCNF.LambdaLifting
// Imports: public import Lean.Compiler.LCNF.Closure public import Lean.Compiler.LCNF.MonadScope public import Lean.Compiler.LCNF.Level public import Lean.Compiler.LCNF.AuxDeclCache
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Code_size(uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineable___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_lam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 101, 74, 224, 114, 167, 47, 177)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_lambdaLifting___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_lambdaLifting___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lambdaLifting"};
static const lean_object* l_Lean_Compiler_LCNF_lambdaLifting___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_lambdaLifting___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 207, 174, 138, 100, 9, 104, 199)}};
static const lean_object* l_Lean_Compiler_LCNF_lambdaLifting___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_lambdaLifting___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_lambdaLifting___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_lambdaLifting = (const lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_elam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 56, 62, 57, 79, 158, 214, 10)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eagerLambdaLifting"};
static const lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value),LEAN_SCALAR_PTR_LITERAL(122, 243, 150, 143, 215, 86, 241, 229)}};
static const lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting = (const lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 70, 220, 104, 162, 210, 125, 97)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LambdaLifting"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 21, 0, 27, 3, 212, 3, 122)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(163, 13, 234, 200, 11, 197, 96, 251)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 32, 36, 94, 50, 116, 19, 243)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 242, 185, 198, 185, 239, 80, 121)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 169, 100, 165, 204, 233, 0, 114)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 11, 57, 42, 15, 159, 79, 187)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 155, 229, 202, 99, 104, 232, 139)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 255, 214, 176, 226, 120, 65, 163)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 193, 88, 177, 192, 62, 195, 60)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 53, 124, 193, 137, 72, 184, 45)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 170, 56, 81, 179, 20, 255, 76)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value),LEAN_SCALAR_PTR_LITERAL(96, 54, 226, 25, 136, 9, 133, 35)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v___y_4_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v_type_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_type_8_ = lean_ctor_get(v___x_7_, 2);
v___x_9_ = 1;
lean_inc_ref(v_type_8_);
v___x_10_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_8_, v___y_4_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_22_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_22_ == 0)
{
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_22_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_22_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
if (lean_obj_tag(v_a_11_) == 0)
{
size_t v___x_15_; size_t v___x_16_; 
lean_del_object(v___x_13_);
v___x_15_ = ((size_t)1ULL);
v___x_16_ = lean_usize_add(v_i_2_, v___x_15_);
v_i_2_ = v___x_16_;
goto _start;
}
else
{
lean_object* v___x_18_; lean_object* v___x_20_; 
lean_dec_ref_known(v_a_11_, 1);
v___x_18_ = lean_box(v___x_9_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_18_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_a_23_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_10_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_10_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = 0;
v___x_32_ = lean_box(v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object* v_as_34_, lean_object* v_i_35_, lean_object* v_stop_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
size_t v_i_boxed_39_; size_t v_stop_boxed_40_; lean_object* v_res_41_; 
v_i_boxed_39_ = lean_unbox_usize(v_i_35_);
lean_dec(v_i_35_);
v_stop_boxed_40_ = lean_unbox_usize(v_stop_36_);
lean_dec(v_stop_36_);
v_res_41_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_34_, v_i_boxed_39_, v_stop_boxed_40_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v_as_34_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object* v_decl_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_params_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_params_48_ = lean_ctor_get(v_decl_42_, 2);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_array_get_size(v_params_48_);
v___x_51_ = lean_nat_dec_lt(v___x_49_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_box(v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
else
{
if (v___x_51_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_box(v___x_51_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
else
{
size_t v___x_56_; size_t v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((size_t)0ULL);
v___x_57_ = lean_usize_of_nat(v___x_50_);
v___x_58_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_params_48_, v___x_56_, v___x_57_, v_a_46_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object* v_decl_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec_ref(v_decl_59_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object* v_as_66_, size_t v_i_67_, size_t v_stop_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_66_, v_i_67_, v_stop_68_, v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object* v_as_75_, lean_object* v_i_76_, lean_object* v_stop_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; lean_object* v_res_85_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_76_);
lean_dec(v_i_76_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_77_);
lean_dec(v_stop_77_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(v_as_75_, v_i_boxed_83_, v_stop_boxed_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec_ref(v_as_75_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object* v_decl_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_value_93_; uint8_t v_liftInstParamOnly_94_; lean_object* v_minSize_95_; uint8_t v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_value_93_ = lean_ctor_get(v_decl_86_, 4);
v_liftInstParamOnly_94_ = lean_ctor_get_uint8(v_a_87_, sizeof(void*)*3);
v_minSize_95_ = lean_ctor_get(v_a_87_, 2);
v___x_96_ = 0;
v___x_97_ = l_Lean_Compiler_LCNF_Code_size(v___x_96_, v_value_93_);
v___x_98_ = lean_nat_dec_lt(v___x_97_, v_minSize_95_);
lean_dec(v___x_97_);
if (v___x_98_ == 0)
{
if (v_liftInstParamOnly_94_ == 0)
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = 1;
v___x_100_ = lean_box(v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_86_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
return v___x_102_;
}
}
else
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = 0;
v___x_104_ = lean_box(v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object* v_decl_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_decl_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec_ref(v_decl_106_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object* v_decl_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_decl_114_, v_a_115_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object* v_decl_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(v_decl_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec_ref(v_decl_124_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; lean_object* v_decls_141_; lean_object* v_nextIdx_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_187_; 
v___x_140_ = lean_st_ref_take(v_a_135_);
v_decls_141_ = lean_ctor_get(v___x_140_, 0);
v_nextIdx_142_ = lean_ctor_get(v___x_140_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_187_ == 0)
{
v___x_144_ = v___x_140_;
v_isShared_145_ = v_isSharedCheck_187_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_nextIdx_142_);
lean_inc(v_decls_141_);
lean_dec(v___x_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_187_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_add(v_nextIdx_142_, v___x_146_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_147_);
v___x_149_ = v___x_144_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_decls_141_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_186_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v_mainDecl_151_; lean_object* v_toSignature_152_; lean_object* v_suffix_153_; lean_object* v_name_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_150_ = lean_st_ref_put(v_a_135_, v___x_149_);
v_mainDecl_151_ = lean_ctor_get(v_a_134_, 1);
v_toSignature_152_ = lean_ctor_get(v_mainDecl_151_, 0);
v_suffix_153_ = lean_ctor_get(v_a_134_, 0);
v_name_154_ = lean_ctor_get(v_toSignature_152_, 0);
lean_inc(v_suffix_153_);
v___x_155_ = lean_name_append_index_after(v_suffix_153_, v_nextIdx_142_);
lean_inc(v_name_154_);
v___x_156_ = l_Lean_Name_append(v_name_154_, v___x_155_);
v___x_157_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_136_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; uint8_t v___x_159_; lean_object* v___x_160_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = lean_unbox(v_a_158_);
lean_dec(v_a_158_);
lean_inc(v___x_156_);
v___x_160_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v___x_156_, v___x_159_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
if (lean_obj_tag(v_a_161_) == 1)
{
lean_dec_ref_known(v_a_161_, 1);
lean_del_object(v___x_163_);
lean_dec(v___x_156_);
goto _start;
}
else
{
lean_object* v___x_167_; 
lean_dec(v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_156_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_156_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec(v___x_156_);
v_a_170_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_160_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_160_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec(v___x_156_);
v_a_178_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_157_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_157_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_195_, v_a_196_, v_a_198_, v_a_200_, v_a_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(lean_object* v_decl_213_, lean_object* v_value_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_fvarId_217_; lean_object* v_binderName_218_; lean_object* v_type_219_; uint8_t v___x_220_; lean_object* v_declNew_221_; lean_object* v___x_222_; lean_object* v_lctx_223_; lean_object* v_nextIdx_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_251_; 
v_fvarId_217_ = lean_ctor_get(v_decl_213_, 0);
v_binderName_218_ = lean_ctor_get(v_decl_213_, 1);
v_type_219_ = lean_ctor_get(v_decl_213_, 3);
v___x_220_ = 0;
lean_inc_ref(v_type_219_);
lean_inc(v_binderName_218_);
lean_inc(v_fvarId_217_);
v_declNew_221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_declNew_221_, 0, v_fvarId_217_);
lean_ctor_set(v_declNew_221_, 1, v_binderName_218_);
lean_ctor_set(v_declNew_221_, 2, v_type_219_);
lean_ctor_set(v_declNew_221_, 3, v_value_214_);
v___x_222_ = lean_st_ref_take(v_a_215_);
v_lctx_223_ = lean_ctor_get(v___x_222_, 0);
v_nextIdx_224_ = lean_ctor_get(v___x_222_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_251_ == 0)
{
v___x_226_ = v___x_222_;
v_isShared_227_ = v_isSharedCheck_251_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_nextIdx_224_);
lean_inc(v_lctx_223_);
lean_dec(v___x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_251_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_inc_ref(v_declNew_221_);
v___x_228_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_220_, v_lctx_223_, v_declNew_221_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_nextIdx_224_);
v___x_230_ = v_reuseFailAlloc_250_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_st_ref_put(v_a_215_, v___x_230_);
v___x_232_ = 1;
v___x_233_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_220_, v_decl_213_, v___x_232_, v_a_215_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v___x_233_, 0);
lean_dec(v_unused_241_);
v___x_235_ = v___x_233_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_dec(v___x_233_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v_declNew_221_);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_declNew_221_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref_known(v_declNew_221_, 4);
v_a_242_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_233_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_233_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(lean_object* v_decl_252_, lean_object* v_value_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_252_, v_value_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_decl_252_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(lean_object* v_decl_257_, lean_object* v_value_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_257_, v_value_258_, v_a_263_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(lean_object* v_decl_268_, lean_object* v_value_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(v_decl_268_, v_value_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec_ref(v_decl_268_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t v_sz_279_, size_t v_i_280_, lean_object* v_bs_281_, uint8_t v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_usize_dec_lt(v_i_280_, v_sz_279_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_bs_281_);
return v___x_290_;
}
else
{
uint8_t v___x_291_; lean_object* v_v_292_; lean_object* v___x_293_; lean_object* v_bs_x27_294_; lean_object* v___x_295_; 
v___x_291_ = 0;
v_v_292_ = lean_array_uget(v_bs_281_, v_i_280_);
v___x_293_ = lean_unsigned_to_nat(0u);
v_bs_x27_294_ = lean_array_uset(v_bs_281_, v_i_280_, v___x_293_);
v___x_295_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_291_, v_v_292_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; size_t v___x_297_; size_t v___x_298_; lean_object* v___x_299_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_add(v_i_280_, v___x_297_);
v___x_299_ = lean_array_uset(v_bs_x27_294_, v_i_280_, v_a_296_);
v_i_280_ = v___x_298_;
v_bs_281_ = v___x_299_;
goto _start;
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v_bs_x27_294_);
v_a_301_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_295_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_295_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object* v_sz_309_, lean_object* v_i_310_, lean_object* v_bs_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
size_t v_sz_boxed_319_; size_t v_i_boxed_320_; uint8_t v___y_2272__boxed_321_; lean_object* v_res_322_; 
v_sz_boxed_319_ = lean_unbox_usize(v_sz_309_);
lean_dec(v_sz_309_);
v_i_boxed_320_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v___y_2272__boxed_321_ = lean_unbox(v___y_312_);
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_boxed_319_, v_i_boxed_320_, v_bs_311_, v___y_2272__boxed_321_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object* v_closure_323_, lean_object* v_decl_324_, lean_object* v_nameNew_325_, uint8_t v_safe_326_, lean_object* v_inlineAttr_x3f_327_, uint8_t v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
uint8_t v___x_335_; size_t v_sz_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_335_ = 0;
v_sz_336_ = lean_array_size(v_closure_323_);
v___x_337_ = ((size_t)0ULL);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_336_, v___x_337_, v_closure_323_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_params_340_; lean_object* v_value_341_; size_t v_sz_342_; lean_object* v___x_343_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v_params_340_ = lean_ctor_get(v_decl_324_, 2);
lean_inc_ref(v_params_340_);
v_value_341_ = lean_ctor_get(v_decl_324_, 4);
lean_inc_ref(v_value_341_);
lean_dec_ref(v_decl_324_);
v_sz_342_ = lean_array_size(v_params_340_);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_342_, v___x_337_, v_params_340_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = l_Array_append___redArg(v_a_339_, v_a_344_);
lean_dec(v_a_344_);
v___x_346_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_335_, v_value_341_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_n(v_a_347_, 2);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_335_, v_a_347_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
lean_inc_ref(v___x_345_);
v___x_350_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_335_, v___x_345_, v_a_349_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_364_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_364_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_364_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_364_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_a_347_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_357_, 0, v_nameNew_325_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
lean_ctor_set(v___x_357_, 2, v_a_351_);
lean_ctor_set(v___x_357_, 3, v___x_345_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*4, v_safe_326_);
v___x_358_ = 0;
v___x_359_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_355_);
lean_ctor_set(v___x_359_, 2, v_inlineAttr_x3f_327_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*3, v___x_358_);
v___x_360_ = l_Lean_Compiler_LCNF_Decl_setLevelParams(v___x_359_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_360_);
v___x_362_ = v___x_353_;
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
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v_a_347_);
lean_dec_ref(v___x_345_);
lean_dec(v_inlineAttr_x3f_327_);
lean_dec(v_nameNew_325_);
v_a_365_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_350_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_350_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_a_347_);
lean_dec_ref(v___x_345_);
lean_dec(v_inlineAttr_x3f_327_);
lean_dec(v_nameNew_325_);
v_a_373_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_348_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_348_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v___x_345_);
lean_dec(v_inlineAttr_x3f_327_);
lean_dec(v_nameNew_325_);
v_a_381_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_346_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_346_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v_value_341_);
lean_dec(v_a_339_);
lean_dec(v_inlineAttr_x3f_327_);
lean_dec(v_nameNew_325_);
v_a_389_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_343_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_343_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_inlineAttr_x3f_327_);
lean_dec(v_nameNew_325_);
lean_dec_ref(v_decl_324_);
v_a_397_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_338_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_338_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object* v_closure_405_, lean_object* v_decl_406_, lean_object* v_nameNew_407_, lean_object* v_safe_408_, lean_object* v_inlineAttr_x3f_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_safe_boxed_417_; uint8_t v_a_boxed_418_; lean_object* v_res_419_; 
v_safe_boxed_417_ = lean_unbox(v_safe_408_);
v_a_boxed_418_ = lean_unbox(v_a_410_);
v_res_419_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_405_, v_decl_406_, v_nameNew_407_, v_safe_boxed_417_, v_inlineAttr_x3f_409_, v_a_boxed_418_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
if (lean_obj_tag(v_a_420_) == 0)
{
lean_object* v___x_422_; 
v___x_422_ = l_List_reverse___redArg(v_a_421_);
return v___x_422_;
}
else
{
lean_object* v_head_423_; lean_object* v_tail_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_head_423_ = lean_ctor_get(v_a_420_, 0);
v_tail_424_ = lean_ctor_get(v_a_420_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v_a_420_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_tail_424_);
lean_inc(v_head_423_);
lean_dec(v_a_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_mkLevelParam(v_head_423_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_a_421_);
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_421_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v_a_420_ = v_tail_424_;
v_a_421_ = v___x_430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t v_sz_434_, size_t v_i_435_, lean_object* v_bs_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_437_ == 0)
{
return v_bs_436_;
}
else
{
lean_object* v_v_438_; lean_object* v_fvarId_439_; lean_object* v___x_440_; lean_object* v_bs_x27_441_; lean_object* v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v_v_438_ = lean_array_uget_borrowed(v_bs_436_, v_i_435_);
v_fvarId_439_ = lean_ctor_get(v_v_438_, 0);
lean_inc(v_fvarId_439_);
v___x_440_ = lean_unsigned_to_nat(0u);
v_bs_x27_441_ = lean_array_uset(v_bs_436_, v_i_435_, v___x_440_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_fvarId_439_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = lean_usize_add(v_i_435_, v___x_443_);
v___x_445_ = lean_array_uset(v_bs_x27_441_, v_i_435_, v___x_442_);
v_i_435_ = v___x_444_;
v_bs_436_ = v___x_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object* v_sz_447_, lean_object* v_i_448_, lean_object* v_bs_449_){
_start:
{
size_t v_sz_boxed_450_; size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_sz_boxed_450_ = lean_unbox_usize(v_sz_447_);
lean_dec(v_sz_447_);
v_i_boxed_451_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_boxed_450_, v_i_boxed_451_, v_bs_449_);
return v_res_452_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_unsigned_to_nat(16u);
v___x_455_ = lean_mk_array(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object* v_closure_459_, lean_object* v_decl_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___y_469_; lean_object* v_auxDeclName_470_; lean_object* v___y_471_; lean_object* v___x_477_; 
v___x_477_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_461_, v_a_462_, v_a_463_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_inlineAttr_x3f_480_; lean_object* v_toSignature_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v_inheritInlineAttrs_550_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v_inheritInlineAttrs_550_ = lean_ctor_get_uint8(v_a_461_, sizeof(void*)*3 + 1);
if (v_inheritInlineAttrs_550_ == 0)
{
lean_object* v_mainDecl_551_; lean_object* v_toSignature_552_; lean_object* v___x_553_; 
v_mainDecl_551_ = lean_ctor_get(v_a_461_, 1);
v_toSignature_552_ = lean_ctor_get(v_mainDecl_551_, 0);
v___x_553_ = lean_box(0);
v_inlineAttr_x3f_480_ = v___x_553_;
v_toSignature_481_ = v_toSignature_552_;
v___y_482_ = v_a_462_;
v___y_483_ = v_a_463_;
v___y_484_ = v_a_464_;
v___y_485_ = v_a_465_;
v___y_486_ = v_a_466_;
goto v___jp_479_;
}
else
{
lean_object* v_mainDecl_554_; lean_object* v_toSignature_555_; lean_object* v_inlineAttr_x3f_556_; 
v_mainDecl_554_ = lean_ctor_get(v_a_461_, 1);
v_toSignature_555_ = lean_ctor_get(v_mainDecl_554_, 0);
v_inlineAttr_x3f_556_ = lean_ctor_get(v_mainDecl_554_, 2);
v_inlineAttr_x3f_480_ = v_inlineAttr_x3f_556_;
v_toSignature_481_ = v_toSignature_555_;
v___y_482_ = v_a_462_;
v___y_483_ = v_a_463_;
v___y_484_ = v_a_464_;
v___y_485_ = v_a_465_;
v___y_486_ = v_a_466_;
goto v___jp_479_;
}
v___jp_479_:
{
uint8_t v_safe_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_safe_487_ = lean_ctor_get_uint8(v_toSignature_481_, sizeof(void*)*4);
v___x_488_ = 0;
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1);
v___x_491_ = 0;
v___x_492_ = lean_st_mk_ref(v___x_490_);
lean_inc(v_inlineAttr_x3f_480_);
lean_inc_ref(v_decl_460_);
lean_inc_ref(v_closure_459_);
v___x_493_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_459_, v_decl_460_, v_a_478_, v_safe_487_, v_inlineAttr_x3f_480_, v___x_491_, v___x_492_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v_toSignature_496_; lean_object* v_name_497_; lean_object* v_levelParams_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_n(v_a_494_, 2);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = lean_st_ref_get(v___x_492_);
lean_dec(v___x_492_);
lean_dec(v___x_495_);
v_toSignature_496_ = lean_ctor_get(v_a_494_, 0);
v_name_497_ = lean_ctor_get(v_toSignature_496_, 0);
v_levelParams_498_ = lean_ctor_get(v_toSignature_496_, 1);
v___x_499_ = lean_box(0);
lean_inc(v_levelParams_498_);
v___x_500_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(v_levelParams_498_, v___x_499_);
v___x_501_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___x_488_, v_a_494_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
if (lean_obj_tag(v_a_502_) == 0)
{
lean_object* v___x_503_; 
lean_inc(v_name_497_);
lean_inc(v_a_494_);
v___x_503_ = l_Lean_Compiler_LCNF_Decl_save(v___x_488_, v_a_494_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; lean_object* v_decls_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref_known(v___x_503_, 1);
v___x_504_ = lean_st_ref_take(v___y_482_);
v_decls_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_504_, 1);
lean_dec(v_unused_515_);
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_decls_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_array_push(v_decls_505_, v_a_494_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_489_);
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_489_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_st_ref_put(v___y_482_, v___x_511_);
v___y_469_ = v___x_500_;
v_auxDeclName_470_ = v_name_497_;
v___y_471_ = v___y_484_;
goto v___jp_468_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v___x_500_);
lean_dec(v_name_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_decl_460_);
lean_dec_ref(v_closure_459_);
v_a_516_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_503_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_503_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v_declName_524_; lean_object* v___x_525_; 
v_declName_524_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_declName_524_);
lean_dec_ref_known(v_a_502_, 1);
v___x_525_ = l_Lean_Compiler_LCNF_eraseDecl(v___x_488_, v_a_494_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_dec_ref_known(v___x_525_, 1);
v___y_469_ = v___x_500_;
v_auxDeclName_470_ = v_declName_524_;
v___y_471_ = v___y_484_;
goto v___jp_468_;
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_declName_524_);
lean_dec(v___x_500_);
lean_dec_ref(v_decl_460_);
lean_dec_ref(v_closure_459_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v___x_500_);
lean_dec(v_a_494_);
lean_dec_ref(v_decl_460_);
lean_dec_ref(v_closure_459_);
v_a_534_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_501_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_501_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v___x_492_);
lean_dec_ref(v_decl_460_);
lean_dec_ref(v_closure_459_);
v_a_542_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_493_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_493_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v_decl_460_);
lean_dec_ref(v_closure_459_);
v_a_557_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_477_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_477_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
v___jp_468_:
{
size_t v_sz_472_; size_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_sz_472_ = lean_array_size(v_closure_459_);
v___x_473_ = ((size_t)0ULL);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_472_, v___x_473_, v_closure_459_);
v___x_475_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_475_, 0, v_auxDeclName_470_);
lean_ctor_set(v___x_475_, 1, v___y_469_);
lean_ctor_set(v___x_475_, 2, v___x_474_);
v___x_476_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_460_, v___x_475_, v___y_471_);
lean_dec_ref(v_decl_460_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object* v_closure_565_, lean_object* v_decl_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_565_, v_decl_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object* v_closure_575_, lean_object* v_decl_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_575_, v_decl_576_, v_a_577_, v_a_578_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object* v_closure_586_, lean_object* v_decl_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(v_closure_586_, v_decl_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(lean_object* v_as_599_, size_t v_sz_600_, size_t v_i_601_, lean_object* v_b_602_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_601_, v_sz_600_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_b_602_);
return v___x_605_;
}
else
{
lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_658_; 
v_snd_606_ = lean_ctor_get(v_b_602_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_b_602_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_b_602_, 0);
lean_dec(v_unused_659_);
v___x_608_ = v_b_602_;
v_isShared_609_ = v_isSharedCheck_658_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_dec(v_b_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_658_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_array_610_; lean_object* v_start_611_; lean_object* v_stop_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_array_610_ = lean_ctor_get(v_snd_606_, 0);
v_start_611_ = lean_ctor_get(v_snd_606_, 1);
v_stop_612_ = lean_ctor_get(v_snd_606_, 2);
v___x_613_ = lean_box(0);
v___x_614_ = lean_nat_dec_lt(v_start_611_, v_stop_612_);
if (v___x_614_ == 0)
{
lean_object* v___x_616_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_613_);
v___x_616_ = v___x_608_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_606_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
else
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_654_; 
lean_inc(v_stop_612_);
lean_inc(v_start_611_);
lean_inc_ref(v_array_610_);
v_isSharedCheck_654_ = !lean_is_exclusive(v_snd_606_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_655_ = lean_ctor_get(v_snd_606_, 2);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_snd_606_, 1);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_snd_606_, 0);
lean_dec(v_unused_657_);
v___x_620_ = v_snd_606_;
v_isShared_621_ = v_isSharedCheck_654_;
goto v_resetjp_619_;
}
else
{
lean_dec(v_snd_606_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_654_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_a_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v_a_622_ = lean_array_uget(v_as_599_, v_i_601_);
v___x_623_ = lean_array_fget(v_array_610_, v_start_611_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_start_611_, v___x_624_);
lean_dec(v_start_611_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_array_610_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_stop_612_);
v___x_627_ = v_reuseFailAlloc_653_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
if (lean_obj_tag(v_a_622_) == 1)
{
lean_object* v_fvarId_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_647_; 
v_fvarId_628_ = lean_ctor_get(v_a_622_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_a_622_);
if (v_isSharedCheck_647_ == 0)
{
v___x_630_ = v_a_622_;
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_fvarId_628_);
lean_dec(v_a_622_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_fvarId_632_; uint8_t v___x_633_; 
v_fvarId_632_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_fvarId_632_);
lean_dec(v___x_623_);
v___x_633_ = l_Lean_instBEqFVarId_beq(v_fvarId_628_, v_fvarId_632_);
lean_dec(v_fvarId_632_);
lean_dec(v_fvarId_628_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_627_);
lean_ctor_set(v___x_608_, 0, v___x_634_);
v___x_636_ = v___x_608_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_627_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 0);
lean_ctor_set(v___x_630_, 0, v___x_636_);
v___x_638_ = v___x_630_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v___x_642_; 
lean_del_object(v___x_630_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_627_);
lean_ctor_set(v___x_608_, 0, v___x_613_);
v___x_642_ = v___x_608_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_627_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
size_t v___x_643_; size_t v___x_644_; 
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_601_, v___x_643_);
v_i_601_ = v___x_644_;
v_b_602_ = v___x_642_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_650_; 
lean_dec(v___x_623_);
lean_dec(v_a_622_);
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_627_);
lean_ctor_set(v___x_608_, 0, v___x_648_);
v___x_650_ = v___x_608_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_627_);
v___x_650_ = v_reuseFailAlloc_652_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(lean_object* v_as_660_, lean_object* v_sz_661_, lean_object* v_i_662_, lean_object* v_b_663_, lean_object* v___y_664_){
_start:
{
size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_sz_boxed_665_ = lean_unbox_usize(v_sz_661_);
lean_dec(v_sz_661_);
v_i_boxed_666_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_660_, v_sz_boxed_665_, v_i_boxed_666_, v_b_663_);
lean_dec_ref(v_as_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(lean_object* v_decl_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
uint8_t v_allowEtaContraction_682_; 
v_allowEtaContraction_682_ = lean_ctor_get_uint8(v_a_671_, sizeof(void*)*3 + 2);
if (v_allowEtaContraction_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref(v_decl_670_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_value_685_; 
v_value_685_ = lean_ctor_get(v_decl_670_, 4);
lean_inc_ref(v_value_685_);
if (lean_obj_tag(v_value_685_) == 0)
{
lean_object* v_decl_686_; lean_object* v_value_687_; 
v_decl_686_ = lean_ctor_get(v_value_685_, 0);
lean_inc_ref(v_decl_686_);
v_value_687_ = lean_ctor_get(v_decl_686_, 3);
lean_inc(v_value_687_);
if (lean_obj_tag(v_value_687_) == 3)
{
lean_object* v_k_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_803_; 
v_k_688_ = lean_ctor_get(v_value_685_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_value_685_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_value_685_, 0);
lean_dec(v_unused_804_);
v___x_690_ = v_value_685_;
v_isShared_691_ = v_isSharedCheck_803_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_k_688_);
lean_dec(v_value_685_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_803_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_k_688_) == 5)
{
lean_object* v_params_692_; lean_object* v_fvarId_693_; lean_object* v_declName_694_; lean_object* v_us_695_; lean_object* v_args_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_802_; 
v_params_692_ = lean_ctor_get(v_decl_670_, 2);
v_fvarId_693_ = lean_ctor_get(v_decl_686_, 0);
lean_inc(v_fvarId_693_);
lean_dec_ref(v_decl_686_);
v_declName_694_ = lean_ctor_get(v_value_687_, 0);
v_us_695_ = lean_ctor_get(v_value_687_, 1);
v_args_696_ = lean_ctor_get(v_value_687_, 2);
v_isSharedCheck_802_ = !lean_is_exclusive(v_value_687_);
if (v_isSharedCheck_802_ == 0)
{
v___x_698_ = v_value_687_;
v_isShared_699_ = v_isSharedCheck_802_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_args_696_);
lean_inc(v_us_695_);
lean_inc(v_declName_694_);
lean_dec(v_value_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_802_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_fvarId_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_801_; 
v_fvarId_700_ = lean_ctor_get(v_k_688_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_k_688_);
if (v_isSharedCheck_801_ == 0)
{
v___x_702_ = v_k_688_;
v_isShared_703_ = v_isSharedCheck_801_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_fvarId_700_);
lean_dec(v_k_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_801_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_instBEqFVarId_beq(v_fvarId_693_, v_fvarId_700_);
lean_dec(v_fvarId_700_);
lean_dec(v_fvarId_693_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_args_696_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_del_object(v___x_690_);
lean_dec_ref(v_decl_670_);
v___x_705_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
lean_ctor_set(v___x_702_, 0, v___x_705_);
v___x_707_ = v___x_702_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_array_get_size(v_args_696_);
v___x_710_ = lean_array_get_size(v_params_692_);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_args_696_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_del_object(v___x_690_);
lean_dec_ref(v_decl_670_);
v___x_712_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
lean_ctor_set(v___x_702_, 0, v___x_712_);
v___x_714_ = v___x_702_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_object* v___x_716_; 
lean_del_object(v___x_702_);
v___x_716_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_674_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; uint8_t v___x_718_; lean_object* v___x_719_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_unbox(v_a_717_);
lean_dec(v_a_717_);
lean_inc(v_declName_694_);
v___x_719_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_694_, v___x_718_, v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_784_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_784_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_784_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_784_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
if (lean_obj_tag(v_a_720_) == 1)
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_722_);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_a_720_, 0);
lean_dec(v_unused_779_);
v___x_725_ = v_a_720_;
v_isShared_726_ = v_isSharedCheck_778_;
goto v_resetjp_724_;
}
else
{
lean_dec(v_a_720_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_778_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_727_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_params_692_);
v___x_728_ = l_Array_toSubarray___redArg(v_params_692_, v___x_727_, v___x_710_);
v___x_729_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_728_);
lean_ctor_set(v___x_690_, 0, v___x_729_);
v___x_731_ = v___x_690_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_728_);
v___x_731_ = v_reuseFailAlloc_777_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
size_t v_sz_732_; size_t v___x_733_; lean_object* v___x_734_; 
v_sz_732_ = lean_array_size(v_args_696_);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_args_696_, v_sz_732_, v___x_733_, v___x_731_);
lean_dec_ref(v_args_696_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_768_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_768_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_768_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_768_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_fst_739_; 
v_fst_739_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_fst_739_);
lean_dec(v_a_735_);
if (lean_obj_tag(v_fst_739_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_del_object(v___x_737_);
v___x_740_ = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0));
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v___x_740_);
v___x_742_ = v___x_698_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_declName_694_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_us_695_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___x_740_);
v___x_742_ = v_reuseFailAlloc_763_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_670_, v___x_742_, v_a_675_);
lean_dec_ref(v_decl_670_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_754_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_754_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_a_744_);
v___x_749_ = v___x_725_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_749_);
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_del_object(v___x_725_);
v_a_755_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_743_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_743_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v_val_764_; lean_object* v___x_766_; 
lean_del_object(v___x_725_);
lean_del_object(v___x_698_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_dec_ref(v_decl_670_);
v_val_764_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_val_764_);
lean_dec_ref_known(v_fst_739_, 1);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_val_764_);
v___x_766_ = v___x_737_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_val_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_del_object(v___x_725_);
lean_del_object(v___x_698_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_dec_ref(v_decl_670_);
v_a_769_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_734_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_734_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v_a_720_);
lean_del_object(v___x_698_);
lean_dec_ref(v_args_696_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_del_object(v___x_690_);
lean_dec_ref(v_decl_670_);
v___x_780_ = lean_box(0);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_780_);
v___x_782_ = v___x_722_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_args_696_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_del_object(v___x_690_);
lean_dec_ref(v_decl_670_);
v_a_785_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_719_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_719_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_args_696_);
lean_dec(v_us_695_);
lean_dec(v_declName_694_);
lean_del_object(v___x_690_);
lean_dec_ref(v_decl_670_);
v_a_793_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_716_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_716_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
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
}
}
}
else
{
lean_del_object(v___x_690_);
lean_dec_ref(v_k_688_);
lean_dec_ref_known(v_value_687_, 3);
lean_dec_ref(v_decl_686_);
lean_dec_ref(v_decl_670_);
goto v___jp_679_;
}
}
}
else
{
lean_dec(v_value_687_);
lean_dec_ref(v_decl_686_);
lean_dec_ref_known(v_value_685_, 2);
lean_dec_ref(v_decl_670_);
goto v___jp_679_;
}
}
else
{
lean_dec_ref(v_value_685_);
lean_dec_ref(v_decl_670_);
goto v___jp_679_;
}
}
v___jp_679_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(lean_object* v_decl_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_decl_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(lean_object* v_as_815_, size_t v_sz_816_, size_t v_i_817_, lean_object* v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_815_, v_sz_816_, v_i_817_, v_b_818_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(lean_object* v_as_828_, lean_object* v_sz_829_, lean_object* v_i_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
size_t v_sz_boxed_840_; size_t v_i_boxed_841_; lean_object* v_res_842_; 
v_sz_boxed_840_ = lean_unbox_usize(v_sz_829_);
lean_dec(v_sz_829_);
v_i_boxed_841_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(v_as_828_, v_sz_boxed_840_, v_i_boxed_841_, v_b_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_as_828_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object* v_as_843_, size_t v_i_844_, size_t v_stop_845_, lean_object* v_b_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_eq(v_i_844_, v_stop_845_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v_fvarId_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; 
v___x_848_ = lean_array_uget_borrowed(v_as_843_, v_i_844_);
v_fvarId_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_fvarId_849_);
v___x_850_ = l_Lean_FVarIdSet_insert(v_b_846_, v_fvarId_849_);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_844_, v___x_851_);
v_i_844_ = v___x_852_;
v_b_846_ = v___x_850_;
goto _start;
}
else
{
return v_b_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object* v_as_854_, lean_object* v_i_855_, lean_object* v_stop_856_, lean_object* v_b_857_){
_start:
{
size_t v_i_boxed_858_; size_t v_stop_boxed_859_; lean_object* v_res_860_; 
v_i_boxed_858_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_stop_boxed_859_ = lean_unbox_usize(v_stop_856_);
lean_dec(v_stop_856_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_as_854_, v_i_boxed_858_, v_stop_boxed_859_, v_b_857_);
lean_dec_ref(v_as_854_);
return v_res_860_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(lean_object* v_k_861_, lean_object* v_t_862_){
_start:
{
if (lean_obj_tag(v_t_862_) == 0)
{
lean_object* v_k_863_; lean_object* v_l_864_; lean_object* v_r_865_; uint8_t v___x_866_; 
v_k_863_ = lean_ctor_get(v_t_862_, 1);
v_l_864_ = lean_ctor_get(v_t_862_, 3);
v_r_865_ = lean_ctor_get(v_t_862_, 4);
v___x_866_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_861_, v_k_863_);
switch(v___x_866_)
{
case 0:
{
v_t_862_ = v_l_864_;
goto _start;
}
case 1:
{
uint8_t v___x_868_; 
v___x_868_ = 1;
return v___x_868_;
}
default: 
{
v_t_862_ = v_r_865_;
goto _start;
}
}
}
else
{
uint8_t v___x_870_; 
v___x_870_ = 0;
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(lean_object* v_k_871_, lean_object* v_t_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_871_, v_t_872_);
lean_dec(v_t_872_);
lean_dec(v_k_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object* v_a_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v___y_876_, v_a_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object* v_a_878_, lean_object* v___y_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(v_a_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v_a_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t v_a_882_, lean_object* v_x_883_){
_start:
{
return v_a_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
uint8_t v_a_12981__boxed_886_; uint8_t v_res_887_; lean_object* v_r_888_; 
v_a_12981__boxed_886_ = lean_unbox(v_a_884_);
v_res_887_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(v_a_12981__boxed_886_, v_x_885_);
lean_dec(v_x_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(lean_object* v_i_889_, lean_object* v_as_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_array_get_size(v_as_890_);
v___x_900_ = lean_nat_dec_lt(v_i_889_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v_i_889_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_as_890_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v_a_904_; 
v_a_902_ = lean_array_fget_borrowed(v_as_890_, v_i_889_);
if (lean_obj_tag(v_a_902_) == 0)
{
lean_object* v_params_915_; lean_object* v_code_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_params_915_ = lean_ctor_get(v_a_902_, 1);
v_code_916_ = lean_ctor_get(v_a_902_, 2);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_array_get_size(v_params_915_);
v___x_919_ = lean_nat_dec_lt(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_inc_ref(v_code_916_);
v___x_920_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_916_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
lean_inc_ref(v_a_902_);
v___x_922_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_902_, v_a_921_);
v_a_904_ = v___x_922_;
goto v___jp_903_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v_as_890_);
lean_dec(v_i_889_);
v_a_923_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_920_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_920_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_931_ = ((size_t)0ULL);
v___x_932_ = lean_usize_of_nat(v___x_918_);
lean_inc(v___y_893_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_915_, v___x_931_, v___x_932_, v___y_893_);
lean_inc_ref(v_code_916_);
v___x_934_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_916_, v___y_891_, v___y_892_, v___x_933_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___x_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
lean_inc_ref(v_a_902_);
v___x_936_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_902_, v_a_935_);
v_a_904_ = v___x_936_;
goto v___jp_903_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_as_890_);
lean_dec(v_i_889_);
v_a_937_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_934_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_934_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
lean_object* v_code_945_; lean_object* v___x_946_; 
v_code_945_ = lean_ctor_get(v_a_902_, 0);
lean_inc_ref(v_code_945_);
v___x_946_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_945_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
lean_inc_ref(v_a_902_);
v___x_948_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_902_, v_a_947_);
v_a_904_ = v___x_948_;
goto v___jp_903_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v_as_890_);
lean_dec(v_i_889_);
v_a_949_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_946_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
v___jp_903_:
{
size_t v___x_905_; size_t v___x_906_; uint8_t v___x_907_; 
v___x_905_ = lean_ptr_addr(v_a_902_);
v___x_906_ = lean_ptr_addr(v_a_904_);
v___x_907_ = lean_usize_dec_eq(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_i_889_, v___x_908_);
v___x_910_ = lean_array_fset(v_as_890_, v_i_889_, v_a_904_);
lean_dec(v_i_889_);
v_i_889_ = v___x_909_;
v_as_890_ = v___x_910_;
goto _start;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v_a_904_);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_nat_add(v_i_889_, v___x_912_);
lean_dec(v_i_889_);
v_i_889_ = v___x_913_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object* v_code_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
switch(lean_obj_tag(v_code_957_))
{
case 0:
{
lean_object* v_decl_966_; lean_object* v_k_967_; lean_object* v_fvarId_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_decl_966_ = lean_ctor_get(v_code_957_, 0);
v_k_967_ = lean_ctor_get(v_code_957_, 1);
v_fvarId_968_ = lean_ctor_get(v_decl_966_, 0);
lean_inc(v_fvarId_968_);
lean_inc(v_a_960_);
v___x_969_ = l_Lean_FVarIdSet_insert(v_a_960_, v_fvarId_968_);
lean_inc_ref(v_k_967_);
v___x_970_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_967_, v_a_958_, v_a_959_, v___x_969_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v___x_969_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1007_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1007_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1007_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
size_t v___x_975_; size_t v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_ptr_addr(v_k_967_);
v___x_976_ = lean_ptr_addr(v_a_971_);
v___x_977_ = lean_usize_dec_eq(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_987_; 
lean_inc_ref(v_decl_966_);
v_isSharedCheck_987_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_988_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_989_);
v___x_979_ = v_code_957_;
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
else
{
lean_dec(v_code_957_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_a_971_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_decl_966_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_a_971_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_982_);
v___x_984_ = v___x_973_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
size_t v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_ptr_addr(v_decl_966_);
v___x_991_ = lean_usize_dec_eq(v___x_990_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1001_; 
lean_inc_ref(v_decl_966_);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; lean_object* v_unused_1003_; 
v_unused_1002_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1003_);
v___x_993_ = v_code_957_;
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_code_957_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_a_971_);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_decl_966_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_971_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_996_);
v___x_998_ = v___x_973_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v___x_1005_; 
lean_dec(v_a_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_code_957_);
v___x_1005_ = v___x_973_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_code_957_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_957_, 2);
return v___x_970_;
}
}
case 1:
{
lean_object* v_decl_1008_; lean_object* v_k_1009_; lean_object* v_declNew_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___f_1031_; lean_object* v___x_1032_; 
v_decl_1008_ = lean_ctor_get(v_code_957_, 0);
v_k_1009_ = lean_ctor_get(v_code_957_, 1);
lean_inc(v_a_960_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1031_, 0, v_a_960_);
lean_inc_ref(v_decl_1008_);
v___x_1032_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_decl_1008_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_a_1033_, v_a_958_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; uint8_t v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = lean_unbox(v_a_1035_);
if (v___x_1036_ == 0)
{
lean_object* v_fvarId_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_a_1035_);
lean_dec_ref(v___f_1031_);
v_fvarId_1037_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_fvarId_1037_);
lean_inc(v_a_960_);
v___x_1038_ = l_Lean_FVarIdSet_insert(v_a_960_, v_fvarId_1037_);
lean_inc_ref(v_k_1009_);
v___x_1039_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1009_, v_a_958_, v_a_959_, v___x_1038_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v___x_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1077_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1077_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1077_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
size_t v___x_1044_; size_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_ptr_addr(v_k_1009_);
v___x_1045_ = lean_ptr_addr(v_a_1040_);
v___x_1046_ = lean_usize_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1056_; 
v_isSharedCheck_1056_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; lean_object* v_unused_1058_; 
v_unused_1057_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1058_);
v___x_1048_ = v_code_957_;
v_isShared_1049_ = v_isSharedCheck_1056_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_code_957_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1056_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_a_1040_);
lean_ctor_set(v___x_1048_, 0, v_a_1033_);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1033_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_a_1040_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1051_);
v___x_1053_ = v___x_1042_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
size_t v___x_1059_; size_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = lean_ptr_addr(v_decl_1008_);
v___x_1060_ = lean_ptr_addr(v_a_1033_);
v___x_1061_ = lean_usize_dec_eq(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1072_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1073_);
v___x_1063_ = v_code_957_;
v_isShared_1064_ = v_isSharedCheck_1071_;
goto v_resetjp_1062_;
}
else
{
lean_dec(v_code_957_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1071_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v_a_1040_);
lean_ctor_set(v___x_1063_, 0, v_a_1033_);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1033_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_a_1040_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1066_);
v___x_1068_ = v___x_1042_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v___x_1075_; 
lean_dec(v_a_1040_);
lean_dec(v_a_1033_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_code_957_);
v___x_1075_ = v___x_1042_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_code_957_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_dec(v_a_1033_);
lean_dec_ref_known(v_code_957_, 2);
return v___x_1039_;
}
}
else
{
lean_object* v___f_1078_; lean_object* v___x_1079_; 
lean_inc_ref(v_k_1009_);
lean_dec_ref_known(v_code_957_, 2);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1078_, 0, v_a_1035_);
lean_inc(v_a_1033_);
v___x_1079_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_a_1033_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
if (lean_obj_tag(v_a_1080_) == 1)
{
lean_object* v_val_1081_; 
lean_dec_ref(v___f_1078_);
lean_dec(v_a_1033_);
lean_dec_ref(v___f_1031_);
v_val_1081_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v_a_1080_, 1);
v_declNew_1011_ = v_val_1081_;
v___y_1012_ = v_a_958_;
v___y_1013_ = v_a_959_;
v___y_1014_ = v_a_960_;
v___y_1015_ = v_a_961_;
v___y_1016_ = v_a_962_;
v___y_1017_ = v_a_963_;
v___y_1018_ = v_a_964_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_a_1080_);
lean_inc(v_a_1033_);
v___x_1082_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed), 8, 1);
lean_closure_set(v___x_1082_, 0, v_a_1033_);
v___x_1083_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v___x_1082_, v___f_1031_, v___f_1078_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v_snd_1085_; lean_object* v_fst_1086_; lean_object* v___x_1087_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v_snd_1085_ = lean_ctor_get(v_a_1084_, 1);
lean_inc(v_snd_1085_);
lean_dec(v_a_1084_);
v_fst_1086_ = lean_ctor_get(v_snd_1085_, 0);
lean_inc(v_fst_1086_);
lean_dec(v_snd_1085_);
v___x_1087_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_fst_1086_, v_a_1033_, v_a_958_, v_a_959_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v_declNew_1011_ = v_a_1088_;
v___y_1012_ = v_a_958_;
v___y_1013_ = v_a_959_;
v___y_1014_ = v_a_960_;
v___y_1015_ = v_a_961_;
v___y_1016_ = v_a_962_;
v___y_1017_ = v_a_963_;
v___y_1018_ = v_a_964_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_k_1009_);
v_a_1089_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_a_1033_);
lean_dec_ref(v_k_1009_);
v_a_1097_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1083_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1083_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___f_1078_);
lean_dec(v_a_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_k_1009_);
v_a_1105_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1079_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1079_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref_known(v_code_957_, 2);
v_a_1113_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1034_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1034_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v___f_1031_);
lean_dec_ref_known(v_code_957_, 2);
v_a_1121_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1032_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1032_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
v___jp_1010_:
{
lean_object* v_fvarId_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_fvarId_1019_ = lean_ctor_get(v_declNew_1011_, 0);
lean_inc(v_fvarId_1019_);
lean_inc(v___y_1014_);
v___x_1020_ = l_Lean_FVarIdSet_insert(v___y_1014_, v_fvarId_1019_);
v___x_1021_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1009_, v___y_1012_, v___y_1013_, v___x_1020_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___x_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_declNew_1011_);
lean_ctor_set(v___x_1026_, 1, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_dec_ref(v_declNew_1011_);
return v___x_1021_;
}
}
}
case 2:
{
lean_object* v_decl_1129_; lean_object* v_k_1130_; lean_object* v___x_1131_; 
v_decl_1129_ = lean_ctor_get(v_code_957_, 0);
v_k_1130_ = lean_ctor_get(v_code_957_, 1);
lean_inc_ref(v_decl_1129_);
v___x_1131_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_decl_1129_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v_fvarId_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v_fvarId_1133_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_fvarId_1133_);
lean_inc(v_a_960_);
v___x_1134_ = l_Lean_FVarIdSet_insert(v_a_960_, v_fvarId_1133_);
lean_inc_ref(v_k_1130_);
v___x_1135_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1130_, v_a_958_, v_a_959_, v___x_1134_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1173_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1173_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1173_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
size_t v___x_1140_; size_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_ptr_addr(v_k_1130_);
v___x_1141_ = lean_ptr_addr(v_a_1136_);
v___x_1142_ = lean_usize_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1152_; 
v_isSharedCheck_1152_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; lean_object* v_unused_1154_; 
v_unused_1153_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1154_);
v___x_1144_ = v_code_957_;
v_isShared_1145_ = v_isSharedCheck_1152_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v_code_957_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1152_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_a_1136_);
lean_ctor_set(v___x_1144_, 0, v_a_1132_);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_a_1136_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1147_);
v___x_1149_ = v___x_1138_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
size_t v___x_1155_; size_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_ptr_addr(v_decl_1129_);
v___x_1156_ = lean_ptr_addr(v_a_1132_);
v___x_1157_ = lean_usize_dec_eq(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1167_; 
v_isSharedCheck_1167_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1168_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1169_);
v___x_1159_ = v_code_957_;
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_code_957_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_a_1136_);
lean_ctor_set(v___x_1159_, 0, v_a_1132_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1132_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_a_1136_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1162_);
v___x_1164_ = v___x_1138_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_a_1136_);
lean_dec(v_a_1132_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_code_957_);
v___x_1171_ = v___x_1138_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_code_957_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
else
{
lean_dec(v_a_1132_);
lean_dec_ref_known(v_code_957_, 2);
return v___x_1135_;
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref_known(v_code_957_, 2);
v_a_1174_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1131_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1131_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
case 4:
{
lean_object* v_cases_1182_; lean_object* v_typeName_1183_; lean_object* v_resultType_1184_; lean_object* v_discr_1185_; lean_object* v_alts_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1225_; 
v_cases_1182_ = lean_ctor_get(v_code_957_, 0);
lean_inc_ref(v_cases_1182_);
v_typeName_1183_ = lean_ctor_get(v_cases_1182_, 0);
v_resultType_1184_ = lean_ctor_get(v_cases_1182_, 1);
v_discr_1185_ = lean_ctor_get(v_cases_1182_, 2);
v_alts_1186_ = lean_ctor_get(v_cases_1182_, 3);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_cases_1182_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1188_ = v_cases_1182_;
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_alts_1186_);
lean_inc(v_discr_1185_);
lean_inc(v_resultType_1184_);
lean_inc(v_typeName_1183_);
lean_dec(v_cases_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1186_);
v___x_1191_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v___x_1190_, v_alts_1186_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1216_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1216_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1216_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
size_t v___x_1196_; size_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = lean_ptr_addr(v_alts_1186_);
lean_dec_ref(v_alts_1186_);
v___x_1197_ = lean_ptr_addr(v_a_1192_);
v___x_1198_ = lean_usize_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1211_; 
v_isSharedCheck_1211_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1212_);
v___x_1200_ = v_code_957_;
v_isShared_1201_ = v_isSharedCheck_1211_;
goto v_resetjp_1199_;
}
else
{
lean_dec(v_code_957_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1211_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 3, v_a_1192_);
v___x_1203_ = v___x_1188_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_typeName_1183_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_resultType_1184_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_discr_1185_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_a_1192_);
v___x_1203_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1205_);
v___x_1207_ = v___x_1194_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
else
{
lean_object* v___x_1214_; 
lean_dec(v_a_1192_);
lean_del_object(v___x_1188_);
lean_dec(v_discr_1185_);
lean_dec_ref(v_resultType_1184_);
lean_dec(v_typeName_1183_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_code_957_);
v___x_1214_ = v___x_1194_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_code_957_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_1188_);
lean_dec_ref(v_alts_1186_);
lean_dec(v_discr_1185_);
lean_dec_ref(v_resultType_1184_);
lean_dec(v_typeName_1183_);
lean_dec_ref_known(v_code_957_, 1);
v_a_1217_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1191_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1191_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
default: 
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_code_957_);
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object* v_funDecl_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_params_1236_; lean_object* v_type_1237_; lean_object* v_value_1238_; uint8_t v___x_1239_; lean_object* v___y_1241_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_params_1236_ = lean_ctor_get(v_funDecl_1227_, 2);
lean_inc_ref(v_params_1236_);
v_type_1237_ = lean_ctor_get(v_funDecl_1227_, 3);
lean_inc_ref(v_type_1237_);
v_value_1238_ = lean_ctor_get(v_funDecl_1227_, 4);
v___x_1239_ = 0;
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_size(v_params_1236_);
v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_inc_ref(v_value_1238_);
v___x_1255_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1238_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
v___y_1241_ = v___x_1255_;
goto v___jp_1240_;
}
else
{
size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = lean_usize_of_nat(v___x_1253_);
lean_inc(v_a_1230_);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1236_, v___x_1256_, v___x_1257_, v_a_1230_);
lean_inc_ref(v_value_1238_);
v___x_1259_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1238_, v_a_1228_, v_a_1229_, v___x_1258_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v___x_1258_);
v___y_1241_ = v___x_1259_;
goto v___jp_1240_;
}
v___jp_1240_:
{
if (lean_obj_tag(v___y_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___y_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___y_1241_, 1);
v___x_1243_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1239_, v_funDecl_1227_, v_type_1237_, v_params_1236_, v_a_1242_, v_a_1232_);
return v___x_1243_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_type_1237_);
lean_dec_ref(v_params_1236_);
lean_dec_ref(v_funDecl_1227_);
v_a_1244_ = lean_ctor_get(v___y_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___y_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___y_1241_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___y_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl___boxed(lean_object* v_funDecl_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_funDecl_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3___boxed(lean_object* v_i_1270_, lean_object* v_as_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v_i_1270_, v_as_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed(lean_object* v_code_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1290_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(lean_object* v_00_u03b2_1291_, lean_object* v_k_1292_, lean_object* v_t_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_1292_, v_t_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_k_1296_, lean_object* v_t_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(v_00_u03b2_1295_, v_k_1296_, v_t_1297_);
lean_dec(v_t_1297_);
lean_dec(v_k_1296_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(lean_object* v_f_1300_, lean_object* v_v_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
if (lean_obj_tag(v_v_1301_) == 0)
{
lean_object* v_code_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1334_; 
v_code_1310_ = lean_ctor_get(v_v_1301_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1312_ = v_v_1301_;
v_isShared_1313_ = v_isSharedCheck_1334_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_code_1310_);
lean_dec(v_v_1301_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1334_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; 
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
v___x_1314_ = lean_apply_9(v_f_1300_, v_code_1310_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, lean_box(0));
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1325_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_a_1315_);
v___x_1320_ = v___x_1312_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1322_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1320_);
v___x_1322_ = v___x_1317_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_del_object(v___x_1312_);
v_a_1326_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1314_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1314_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
else
{
lean_object* v___x_1335_; 
lean_dec_ref(v_f_1300_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_v_1301_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg___boxed(lean_object* v_f_1336_, lean_object* v_v_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1336_, v_v_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(uint8_t v_pu_1347_, lean_object* v_f_1348_, lean_object* v_v_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1348_, v_v_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___boxed(lean_object* v_pu_1359_, lean_object* v_f_1360_, lean_object* v_v_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_pu_boxed_1370_; lean_object* v_res_1371_; 
v_pu_boxed_1370_ = lean_unbox(v_pu_1359_);
v_res_1371_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(v_pu_boxed_1370_, v_f_1360_, v_v_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object* v_decl_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_toSignature_1382_; lean_object* v_value_1383_; uint8_t v_recursive_1384_; lean_object* v_inlineAttr_x3f_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1420_; 
v_toSignature_1382_ = lean_ctor_get(v_decl_1373_, 0);
v_value_1383_ = lean_ctor_get(v_decl_1373_, 1);
v_recursive_1384_ = lean_ctor_get_uint8(v_decl_1373_, sizeof(void*)*3);
v_inlineAttr_x3f_1385_ = lean_ctor_get(v_decl_1373_, 2);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_decl_1373_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1387_ = v_decl_1373_;
v_isShared_1388_ = v_isSharedCheck_1420_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_inlineAttr_x3f_1385_);
lean_inc(v_value_1383_);
lean_inc(v_toSignature_1382_);
lean_dec(v_decl_1373_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1420_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___y_1390_; lean_object* v_params_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_params_1410_ = lean_ctor_get(v_toSignature_1382_, 3);
v___x_1411_ = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0));
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_params_1410_);
v___x_1414_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1411_, v_value_1383_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
v___y_1390_ = v___x_1415_;
goto v___jp_1389_;
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1413_);
lean_inc(v_a_1376_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1410_, v___x_1416_, v___x_1417_, v_a_1376_);
v___x_1419_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1411_, v_value_1383_, v_a_1374_, v_a_1375_, v___x_1418_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v___x_1418_);
v___y_1390_ = v___x_1419_;
goto v___jp_1389_;
}
v___jp_1389_:
{
if (lean_obj_tag(v___y_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1401_; 
v_a_1391_ = lean_ctor_get(v___y_1390_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1393_ = v___y_1390_;
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___y_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v_a_1391_);
v___x_1396_ = v___x_1387_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_toSignature_1382_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_a_1391_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_inlineAttr_x3f_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*3, v_recursive_1384_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1387_);
lean_dec(v_inlineAttr_x3f_1385_);
lean_dec_ref(v_toSignature_1382_);
v_a_1402_ = lean_ctor_get(v___y_1390_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___y_1390_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___y_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___boxed(lean_object* v_decl_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object* v_decl_1436_, uint8_t v_liftInstParamOnly_1437_, uint8_t v_allowEtaContraction_1438_, lean_object* v_suffix_1439_, uint8_t v_inheritInlineAttrs_1440_, lean_object* v_minSize_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_ctx_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1447_ = lean_box(1);
lean_inc_ref(v_decl_1436_);
v_ctx_1448_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ctx_1448_, 0, v_suffix_1439_);
lean_ctor_set(v_ctx_1448_, 1, v_decl_1436_);
lean_ctor_set(v_ctx_1448_, 2, v_minSize_1441_);
lean_ctor_set_uint8(v_ctx_1448_, sizeof(void*)*3, v_liftInstParamOnly_1437_);
lean_ctor_set_uint8(v_ctx_1448_, sizeof(void*)*3 + 1, v_inheritInlineAttrs_1440_);
lean_ctor_set_uint8(v_ctx_1448_, sizeof(void*)*3 + 2, v_allowEtaContraction_1438_);
v___x_1449_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1));
v___x_1450_ = lean_st_mk_ref(v___x_1449_);
v___x_1451_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1436_, v_ctx_1448_, v___x_1450_, v___x_1447_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec_ref_known(v_ctx_1448_, 3);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v_decls_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1456_ = lean_st_ref_get(v___x_1450_);
lean_dec(v___x_1450_);
v_decls_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_decls_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = lean_array_push(v_decls_1457_, v_a_1452_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1458_);
v___x_1460_ = v___x_1454_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v___x_1450_);
v_a_1463_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1451_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1451_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object* v_decl_1471_, lean_object* v_liftInstParamOnly_1472_, lean_object* v_allowEtaContraction_1473_, lean_object* v_suffix_1474_, lean_object* v_inheritInlineAttrs_1475_, lean_object* v_minSize_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
uint8_t v_liftInstParamOnly_boxed_1482_; uint8_t v_allowEtaContraction_boxed_1483_; uint8_t v_inheritInlineAttrs_boxed_1484_; lean_object* v_res_1485_; 
v_liftInstParamOnly_boxed_1482_ = lean_unbox(v_liftInstParamOnly_1472_);
v_allowEtaContraction_boxed_1483_ = lean_unbox(v_allowEtaContraction_1473_);
v_inheritInlineAttrs_boxed_1484_ = lean_unbox(v_inheritInlineAttrs_1475_);
v_res_1485_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v_decl_1471_, v_liftInstParamOnly_boxed_1482_, v_allowEtaContraction_boxed_1483_, v_suffix_1474_, v_inheritInlineAttrs_boxed_1484_, v_minSize_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(lean_object* v_as_1489_, size_t v_i_1490_, size_t v_stop_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_eq(v_i_1490_, v_stop_1491_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_array_uget_borrowed(v_as_1489_, v_i_1490_);
v___x_1501_ = 1;
v___x_1502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1));
lean_inc(v___x_1500_);
v___x_1503_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v___x_1500_, v___x_1498_, v___x_1501_, v___x_1502_, v___x_1498_, v___x_1499_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = l_Array_append___redArg(v_b_1492_, v_a_1504_);
lean_dec(v_a_1504_);
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1490_, v___x_1506_);
v_i_1490_ = v___x_1507_;
v_b_1492_ = v___x_1505_;
goto _start;
}
else
{
lean_dec_ref(v_b_1492_);
return v___x_1503_;
}
}
else
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_b_1492_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object* v_as_1510_, lean_object* v_i_1511_, lean_object* v_stop_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
size_t v_i_boxed_1519_; size_t v_stop_boxed_1520_; lean_object* v_res_1521_; 
v_i_boxed_1519_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_stop_boxed_1520_ = lean_unbox_usize(v_stop_1512_);
lean_dec(v_stop_1512_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_as_1510_, v_i_boxed_1519_, v_stop_boxed_1520_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_as_1510_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object* v___x_1522_, lean_object* v_decls_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_mk_empty_array_with_capacity(v___x_1522_);
v___x_1530_ = lean_array_get_size(v_decls_1523_);
v___x_1531_ = lean_nat_dec_lt(v___x_1522_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1529_);
return v___x_1532_;
}
else
{
size_t v___x_1533_; size_t v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = ((size_t)0ULL);
v___x_1534_ = lean_usize_of_nat(v___x_1530_);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_1523_, v___x_1533_, v___x_1534_, v___x_1529_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object* v___x_1536_, lean_object* v_decls_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(v___x_1536_, v_decls_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_decls_1537_);
lean_dec(v___x_1536_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object* v_declName_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v_env_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1559_ = lean_st_ref_get(v___y_1557_);
v_env_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc_ref(v_env_1560_);
lean_dec(v___x_1559_);
v___x_1561_ = l_Lean_isInstanceReducibleCore(v_env_1560_, v_declName_1556_);
v___x_1562_ = lean_box(v___x_1561_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object* v_declName_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1564_, v___y_1565_);
lean_dec(v___y_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object* v_declName_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1568_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object* v_declName_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(v_declName_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(lean_object* v_as_1585_, size_t v_i_1586_, size_t v_stop_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_a_1595_; uint8_t v___x_1599_; 
v___x_1599_ = lean_usize_dec_eq(v_i_1586_, v_stop_1587_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v_toSignature_1601_; lean_object* v_name_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1600_ = lean_array_uget_borrowed(v_as_1585_, v_i_1586_);
v_toSignature_1601_ = lean_ctor_get(v___x_1600_, 0);
v_name_1602_ = lean_ctor_get(v_toSignature_1601_, 0);
v___x_1603_ = lean_unsigned_to_nat(0u);
lean_inc(v_name_1602_);
v___x_1604_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_name_1602_, v___y_1592_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; uint8_t v___x_1608_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1608_ = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(v___x_1600_);
if (v___x_1608_ == 0)
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_unbox(v_a_1605_);
lean_dec(v_a_1605_);
if (v___x_1609_ == 0)
{
uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = 1;
v___x_1611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1));
lean_inc(v___x_1600_);
v___x_1612_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v___x_1600_, v___x_1610_, v___x_1599_, v___x_1611_, v___x_1599_, v___x_1603_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = l_Array_append___redArg(v_b_1588_, v_a_1613_);
lean_dec(v_a_1613_);
v_a_1595_ = v___x_1614_;
goto v___jp_1594_;
}
else
{
lean_dec_ref(v_b_1588_);
return v___x_1612_;
}
}
else
{
goto v___jp_1606_;
}
}
else
{
lean_dec(v_a_1605_);
goto v___jp_1606_;
}
v___jp_1606_:
{
lean_object* v___x_1607_; 
lean_inc(v___x_1600_);
v___x_1607_ = lean_array_push(v_b_1588_, v___x_1600_);
v_a_1595_ = v___x_1607_;
goto v___jp_1594_;
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_b_1588_);
v_a_1615_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1604_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1604_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_b_1588_);
return v___x_1623_;
}
v___jp_1594_:
{
size_t v___x_1596_; size_t v___x_1597_; 
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1586_, v___x_1596_);
v_i_1586_ = v___x_1597_;
v_b_1588_ = v_a_1595_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___boxed(lean_object* v_as_1624_, lean_object* v_i_1625_, lean_object* v_stop_1626_, lean_object* v_b_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
size_t v_i_boxed_1633_; size_t v_stop_boxed_1634_; lean_object* v_res_1635_; 
v_i_boxed_1633_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_stop_boxed_1634_ = lean_unbox_usize(v_stop_1626_);
lean_dec(v_stop_1626_);
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_as_1624_, v_i_boxed_1633_, v_stop_boxed_1634_, v_b_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_as_1624_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object* v___x_1636_, lean_object* v_decls_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_mk_empty_array_with_capacity(v___x_1636_);
v___x_1644_ = lean_array_get_size(v_decls_1637_);
v___x_1645_ = lean_nat_dec_lt(v___x_1636_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1643_);
return v___x_1646_;
}
else
{
size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = lean_usize_of_nat(v___x_1644_);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_1637_, v___x_1647_, v___x_1648_, v___x_1643_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object* v___x_1650_, lean_object* v_decls_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(v___x_1650_, v_decls_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v_decls_1651_);
lean_dec(v___x_1650_);
return v_res_1657_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_unsigned_to_nat(4205464346u);
v___x_1726_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1727_ = l_Lean_Name_num___override(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1730_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1731_ = l_Lean_Name_str___override(v___x_1730_, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1734_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1735_ = l_Lean_Name_str___override(v___x_1734_, v___x_1733_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(2u);
v___x_1737_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1738_ = l_Lean_Name_num___override(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1744_ = 1;
v___x_1745_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1746_ = l_Lean_registerTraceClass(v___x_1743_, v___x_1744_, v___x_1745_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1747_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1748_ = l_Lean_registerTraceClass(v___x_1747_, v___x_1744_, v___x_1745_);
return v___x_1748_;
}
else
{
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
return v_res_1750_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Level(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Level(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
}
#ifdef __cplusplus
}
#endif
