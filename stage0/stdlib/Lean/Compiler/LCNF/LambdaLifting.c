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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v___y_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v_res_34_;
v_res_34_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_1_, v_i_2_, v_stop_3_, v___y_4_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object* v_as_35_, lean_object* v_i_36_, lean_object* v_stop_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
size_t v_i_boxed_40_; size_t v_stop_boxed_41_; lean_object* v_res_42_; 
v_i_boxed_40_ = lean_unbox_usize(v_i_36_);
lean_dec(v_i_36_);
v_stop_boxed_41_ = lean_unbox_usize(v_stop_37_);
lean_dec(v_stop_37_);
v_res_42_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_35_, v_i_boxed_40_, v_stop_boxed_41_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v_as_35_);
return v_res_42_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object* v_decl_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_params_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_params_49_ = lean_ctor_get(v_decl_43_, 2);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_array_get_size(v_params_49_);
v___x_52_ = lean_nat_dec_lt(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_box(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
else
{
if (v___x_52_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_box(v___x_52_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
else
{
size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((size_t)0ULL);
v___x_58_ = lean_usize_of_nat(v___x_51_);
v___x_59_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_params_49_, v___x_57_, v___x_58_, v_a_47_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_43_ = stack[0].m_obj;
lean_object* v_a_44_ = stack[1].m_obj;
lean_object* v_a_45_ = stack[2].m_obj;
lean_object* v_a_46_ = stack[3].m_obj;
lean_object* v_a_47_ = stack[4].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object* v_decl_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec_ref(v_decl_61_);
return v_res_67_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object* v_as_68_, size_t v_i_69_, size_t v_stop_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_68_, v_i_69_, v_stop_70_, v___y_74_);
return v___x_76_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_68_ = stack[0].m_obj;
size_t v_i_69_ = stack[1].m_num;
size_t v_stop_70_ = stack[2].m_num;
lean_object* v___y_71_ = stack[3].m_obj;
lean_object* v___y_72_ = stack[4].m_obj;
lean_object* v___y_73_ = stack[5].m_obj;
lean_object* v___y_74_ = stack[6].m_obj;
lean_object* v_res_77_;
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(v_as_68_, v_i_69_, v_stop_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object* v_as_78_, lean_object* v_i_79_, lean_object* v_stop_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; lean_object* v_res_88_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_80_);
lean_dec(v_stop_80_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(v_as_78_, v_i_boxed_86_, v_stop_boxed_87_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_as_78_);
return v_res_88_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object* v_decl_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_value_96_; uint8_t v_liftInstParamOnly_97_; lean_object* v_minSize_98_; uint8_t v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_value_96_ = lean_ctor_get(v_decl_89_, 4);
v_liftInstParamOnly_97_ = lean_ctor_get_uint8(v_a_90_, sizeof(void*)*3);
v_minSize_98_ = lean_ctor_get(v_a_90_, 2);
v___x_99_ = 0;
v___x_100_ = l_Lean_Compiler_LCNF_Code_size(v___x_99_, v_value_96_);
v___x_101_ = lean_nat_dec_lt(v___x_100_, v_minSize_98_);
lean_dec(v___x_100_);
if (v___x_101_ == 0)
{
if (v_liftInstParamOnly_97_ == 0)
{
uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = 1;
v___x_103_ = lean_box(v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_89_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
return v___x_105_;
}
}
else
{
uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = 0;
v___x_107_ = lean_box(v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_89_ = stack[0].m_obj;
lean_object* v_a_90_ = stack[1].m_obj;
lean_object* v_a_91_ = stack[2].m_obj;
lean_object* v_a_92_ = stack[3].m_obj;
lean_object* v_a_93_ = stack[4].m_obj;
lean_object* v_a_94_ = stack[5].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_decl_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object* v_decl_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_decl_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec_ref(v_decl_110_);
return v_res_117_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object* v_decl_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_decl_118_, v_a_119_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_shouldLift_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_118_ = stack[0].m_obj;
lean_object* v_a_119_ = stack[1].m_obj;
lean_object* v_a_120_ = stack[2].m_obj;
lean_object* v_a_121_ = stack[3].m_obj;
lean_object* v_a_122_ = stack[4].m_obj;
lean_object* v_a_123_ = stack[5].m_obj;
lean_object* v_a_124_ = stack[6].m_obj;
lean_object* v_a_125_ = stack[7].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(v_decl_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object* v_decl_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(v_decl_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec_ref(v_decl_129_);
return v_res_138_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_decls_146_; lean_object* v_nextIdx_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_192_; 
v___x_145_ = lean_st_ref_take(v_a_140_);
v_decls_146_ = lean_ctor_get(v___x_145_, 0);
v_nextIdx_147_ = lean_ctor_get(v___x_145_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_192_ == 0)
{
v___x_149_ = v___x_145_;
v_isShared_150_ = v_isSharedCheck_192_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_nextIdx_147_);
lean_inc(v_decls_146_);
lean_dec(v___x_145_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_192_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_nextIdx_147_, v___x_151_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_152_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_decls_146_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_191_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v_mainDecl_156_; lean_object* v_toSignature_157_; lean_object* v_suffix_158_; lean_object* v_name_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_155_ = lean_st_ref_put(v_a_140_, v___x_154_);
v_mainDecl_156_ = lean_ctor_get(v_a_139_, 1);
v_toSignature_157_ = lean_ctor_get(v_mainDecl_156_, 0);
v_suffix_158_ = lean_ctor_get(v_a_139_, 0);
v_name_159_ = lean_ctor_get(v_toSignature_157_, 0);
lean_inc(v_suffix_158_);
v___x_160_ = lean_name_append_index_after(v_suffix_158_, v_nextIdx_147_);
lean_inc(v_name_159_);
v___x_161_ = l_Lean_Name_append(v_name_159_, v___x_160_);
v___x_162_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_141_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; uint8_t v___x_164_; lean_object* v___x_165_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = lean_unbox(v_a_163_);
lean_dec(v_a_163_);
lean_inc(v___x_161_);
v___x_165_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v___x_161_, v___x_164_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_174_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_174_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
if (lean_obj_tag(v_a_166_) == 1)
{
lean_dec_ref_known(v_a_166_, 1);
lean_del_object(v___x_168_);
lean_dec(v___x_161_);
goto _start;
}
else
{
lean_object* v___x_172_; 
lean_dec(v_a_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_161_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_161_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v___x_161_);
v_a_175_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_165_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_165_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec(v___x_161_);
v_a_183_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_162_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_162_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_139_ = stack[0].m_obj;
lean_object* v_a_140_ = stack[1].m_obj;
lean_object* v_a_141_ = stack[2].m_obj;
lean_object* v_a_142_ = stack[3].m_obj;
lean_object* v_a_143_ = stack[4].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_200_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_201_, v_a_202_, v_a_204_, v_a_206_, v_a_207_);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_201_ = stack[0].m_obj;
lean_object* v_a_202_ = stack[1].m_obj;
lean_object* v_a_203_ = stack[2].m_obj;
lean_object* v_a_204_ = stack[3].m_obj;
lean_object* v_a_205_ = stack[4].m_obj;
lean_object* v_a_206_ = stack[5].m_obj;
lean_object* v_a_207_ = stack[6].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_219_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(lean_object* v_decl_220_, lean_object* v_value_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_fvarId_224_; lean_object* v_binderName_225_; lean_object* v_type_226_; uint8_t v___x_227_; lean_object* v_declNew_228_; lean_object* v___x_229_; lean_object* v_lctx_230_; lean_object* v_nextIdx_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_258_; 
v_fvarId_224_ = lean_ctor_get(v_decl_220_, 0);
v_binderName_225_ = lean_ctor_get(v_decl_220_, 1);
v_type_226_ = lean_ctor_get(v_decl_220_, 3);
v___x_227_ = 0;
lean_inc_ref(v_type_226_);
lean_inc(v_binderName_225_);
lean_inc(v_fvarId_224_);
v_declNew_228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_declNew_228_, 0, v_fvarId_224_);
lean_ctor_set(v_declNew_228_, 1, v_binderName_225_);
lean_ctor_set(v_declNew_228_, 2, v_type_226_);
lean_ctor_set(v_declNew_228_, 3, v_value_221_);
v___x_229_ = lean_st_ref_take(v_a_222_);
v_lctx_230_ = lean_ctor_get(v___x_229_, 0);
v_nextIdx_231_ = lean_ctor_get(v___x_229_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_258_ == 0)
{
v___x_233_ = v___x_229_;
v_isShared_234_ = v_isSharedCheck_258_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_nextIdx_231_);
lean_inc(v_lctx_230_);
lean_dec(v___x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_258_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_inc_ref(v_declNew_228_);
v___x_235_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_227_, v_lctx_230_, v_declNew_228_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextIdx_231_);
v___x_237_ = v_reuseFailAlloc_257_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_put(v_a_222_, v___x_237_);
v___x_239_ = 1;
v___x_240_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_227_, v_decl_220_, v___x_239_, v_a_222_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v___x_240_, 0);
lean_dec(v_unused_248_);
v___x_242_ = v___x_240_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_dec(v___x_240_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v_declNew_228_);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_declNew_228_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref_known(v_declNew_228_, 4);
v_a_249_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_240_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_240_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_220_ = stack[0].m_obj;
lean_object* v_value_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_220_, v_value_221_, v_a_222_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(lean_object* v_decl_260_, lean_object* v_value_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_260_, v_value_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_decl_260_);
return v_res_264_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(lean_object* v_decl_265_, lean_object* v_value_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_265_, v_value_266_, v_a_271_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_265_ = stack[0].m_obj;
lean_object* v_value_266_ = stack[1].m_obj;
lean_object* v_a_267_ = stack[2].m_obj;
lean_object* v_a_268_ = stack[3].m_obj;
lean_object* v_a_269_ = stack[4].m_obj;
lean_object* v_a_270_ = stack[5].m_obj;
lean_object* v_a_271_ = stack[6].m_obj;
lean_object* v_a_272_ = stack[7].m_obj;
lean_object* v_a_273_ = stack[8].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(v_decl_265_, v_value_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(lean_object* v_decl_277_, lean_object* v_value_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(v_decl_277_, v_value_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec_ref(v_decl_277_);
return v_res_287_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t v_sz_288_, size_t v_i_289_, lean_object* v_bs_290_, uint8_t v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_lt(v_i_289_, v_sz_288_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v_bs_290_);
return v___x_299_;
}
else
{
uint8_t v___x_300_; lean_object* v_v_301_; lean_object* v___x_302_; lean_object* v_bs_x27_303_; lean_object* v___x_304_; 
v___x_300_ = 0;
v_v_301_ = lean_array_uget(v_bs_290_, v_i_289_);
v___x_302_ = lean_unsigned_to_nat(0u);
v_bs_x27_303_ = lean_array_uset(v_bs_290_, v_i_289_, v___x_302_);
v___x_304_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_300_, v_v_301_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_add(v_i_289_, v___x_306_);
v___x_308_ = lean_array_uset(v_bs_x27_303_, v_i_289_, v_a_305_);
v_i_289_ = v___x_307_;
v_bs_290_ = v___x_308_;
goto _start;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v_bs_x27_303_);
v_a_310_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_304_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_304_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_288_ = stack[0].m_num;
size_t v_i_289_ = stack[1].m_num;
lean_object* v_bs_290_ = stack[2].m_obj;
uint8_t v___y_291_ = stack[3].m_num;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v___y_293_ = stack[5].m_obj;
lean_object* v___y_294_ = stack[6].m_obj;
lean_object* v___y_295_ = stack[7].m_obj;
lean_object* v___y_296_ = stack[8].m_obj;
lean_object* v_res_318_;
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_288_, v_i_289_, v_bs_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object* v_sz_319_, lean_object* v_i_320_, lean_object* v_bs_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
size_t v_sz_boxed_329_; size_t v_i_boxed_330_; uint8_t v___y_2272__boxed_331_; lean_object* v_res_332_; 
v_sz_boxed_329_ = lean_unbox_usize(v_sz_319_);
lean_dec(v_sz_319_);
v_i_boxed_330_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v___y_2272__boxed_331_ = lean_unbox(v___y_322_);
v_res_332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_boxed_329_, v_i_boxed_330_, v_bs_321_, v___y_2272__boxed_331_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
return v_res_332_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object* v_closure_333_, lean_object* v_decl_334_, lean_object* v_nameNew_335_, uint8_t v_safe_336_, lean_object* v_inlineAttr_x3f_337_, uint8_t v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
uint8_t v___x_345_; size_t v_sz_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_345_ = 0;
v_sz_346_ = lean_array_size(v_closure_333_);
v___x_347_ = ((size_t)0ULL);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_346_, v___x_347_, v_closure_333_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v_params_350_; lean_object* v_value_351_; size_t v_sz_352_; lean_object* v___x_353_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v_params_350_ = lean_ctor_get(v_decl_334_, 2);
lean_inc_ref(v_params_350_);
v_value_351_ = lean_ctor_get(v_decl_334_, 4);
lean_inc_ref(v_value_351_);
lean_dec_ref(v_decl_334_);
v_sz_352_ = lean_array_size(v_params_350_);
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_352_, v___x_347_, v_params_350_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v___x_355_ = l_Array_append___redArg(v_a_349_, v_a_354_);
lean_dec(v_a_354_);
v___x_356_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_345_, v_value_351_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_358_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_n(v_a_357_, 2);
lean_dec_ref_known(v___x_356_, 1);
v___x_358_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_345_, v_a_357_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
lean_inc_ref(v___x_355_);
v___x_360_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_345_, v___x_355_, v_a_359_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_359_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_374_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_374_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_374_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_374_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_a_357_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_367_, 0, v_nameNew_335_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
lean_ctor_set(v___x_367_, 2, v_a_361_);
lean_ctor_set(v___x_367_, 3, v___x_355_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*4, v_safe_336_);
v___x_368_ = 0;
v___x_369_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_365_);
lean_ctor_set(v___x_369_, 2, v_inlineAttr_x3f_337_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*3, v___x_368_);
v___x_370_ = l_Lean_Compiler_LCNF_Decl_setLevelParams(v___x_369_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_370_);
v___x_372_ = v___x_363_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_357_);
lean_dec_ref(v___x_355_);
lean_dec(v_inlineAttr_x3f_337_);
lean_dec(v_nameNew_335_);
v_a_375_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_360_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_360_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_357_);
lean_dec_ref(v___x_355_);
lean_dec(v_inlineAttr_x3f_337_);
lean_dec(v_nameNew_335_);
v_a_383_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_358_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_358_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
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
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v___x_355_);
lean_dec(v_inlineAttr_x3f_337_);
lean_dec(v_nameNew_335_);
v_a_391_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_356_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_356_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v_value_351_);
lean_dec(v_a_349_);
lean_dec(v_inlineAttr_x3f_337_);
lean_dec(v_nameNew_335_);
v_a_399_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_353_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_353_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_inlineAttr_x3f_337_);
lean_dec(v_nameNew_335_);
lean_dec_ref(v_decl_334_);
v_a_407_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_348_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_348_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_closure_333_ = stack[0].m_obj;
lean_object* v_decl_334_ = stack[1].m_obj;
lean_object* v_nameNew_335_ = stack[2].m_obj;
uint8_t v_safe_336_ = stack[3].m_num;
lean_object* v_inlineAttr_x3f_337_ = stack[4].m_obj;
uint8_t v_a_338_ = stack[5].m_num;
lean_object* v_a_339_ = stack[6].m_obj;
lean_object* v_a_340_ = stack[7].m_obj;
lean_object* v_a_341_ = stack[8].m_obj;
lean_object* v_a_342_ = stack[9].m_obj;
lean_object* v_a_343_ = stack[10].m_obj;
lean_object* v_res_415_;
v_res_415_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_333_, v_decl_334_, v_nameNew_335_, v_safe_336_, v_inlineAttr_x3f_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object* v_closure_416_, lean_object* v_decl_417_, lean_object* v_nameNew_418_, lean_object* v_safe_419_, lean_object* v_inlineAttr_x3f_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
uint8_t v_safe_boxed_428_; uint8_t v_a_boxed_429_; lean_object* v_res_430_; 
v_safe_boxed_428_ = lean_unbox(v_safe_419_);
v_a_boxed_429_ = lean_unbox(v_a_421_);
v_res_430_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_416_, v_decl_417_, v_nameNew_418_, v_safe_boxed_428_, v_inlineAttr_x3f_420_, v_a_boxed_429_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = l_List_reverse___redArg(v_a_432_);
return v___x_433_;
}
else
{
lean_object* v_head_434_; lean_object* v_tail_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_444_; 
v_head_434_ = lean_ctor_get(v_a_431_, 0);
v_tail_435_ = lean_ctor_get(v_a_431_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_444_ == 0)
{
v___x_437_ = v_a_431_;
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_tail_435_);
lean_inc(v_head_434_);
lean_dec(v_a_431_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = l_Lean_mkLevelParam(v_head_434_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_a_432_);
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_a_432_);
v___x_441_ = v_reuseFailAlloc_443_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v_a_431_ = v_tail_435_;
v_a_432_ = v___x_441_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t v_sz_445_, size_t v_i_446_, lean_object* v_bs_447_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = lean_usize_dec_lt(v_i_446_, v_sz_445_);
if (v___x_448_ == 0)
{
return v_bs_447_;
}
else
{
lean_object* v_v_449_; lean_object* v_fvarId_450_; lean_object* v___x_451_; lean_object* v_bs_x27_452_; lean_object* v___x_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
v_v_449_ = lean_array_uget_borrowed(v_bs_447_, v_i_446_);
v_fvarId_450_ = lean_ctor_get(v_v_449_, 0);
lean_inc(v_fvarId_450_);
v___x_451_ = lean_unsigned_to_nat(0u);
v_bs_x27_452_ = lean_array_uset(v_bs_447_, v_i_446_, v___x_451_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_fvarId_450_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_446_, v___x_454_);
v___x_456_ = lean_array_uset(v_bs_x27_452_, v_i_446_, v___x_453_);
v_i_446_ = v___x_455_;
v_bs_447_ = v___x_456_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_445_ = stack[0].m_num;
size_t v_i_446_ = stack[1].m_num;
lean_object* v_bs_447_ = stack[2].m_obj;
lean_object* v_res_458_;
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_445_, v_i_446_, v_bs_447_);
stack->m_obj
 = v_res_458_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object* v_sz_459_, lean_object* v_i_460_, lean_object* v_bs_461_){
_start:
{
size_t v_sz_boxed_462_; size_t v_i_boxed_463_; lean_object* v_res_464_; 
v_sz_boxed_462_ = lean_unbox_usize(v_sz_459_);
lean_dec(v_sz_459_);
v_i_boxed_463_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_res_464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_boxed_462_, v_i_boxed_463_, v_bs_461_);
return v_res_464_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = lean_unsigned_to_nat(16u);
v___x_467_ = lean_mk_array(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object* v_closure_471_, lean_object* v_decl_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___y_481_; lean_object* v_auxDeclName_482_; lean_object* v___y_483_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v_a_496_; lean_object* v___x_544_; 
v___x_544_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_473_, v_a_474_, v_a_475_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v_inlineAttr_x3f_547_; lean_object* v_toSignature_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; uint8_t v_inheritInlineAttrs_571_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v_inheritInlineAttrs_571_ = lean_ctor_get_uint8(v_a_473_, sizeof(void*)*3 + 1);
if (v_inheritInlineAttrs_571_ == 0)
{
lean_object* v_mainDecl_572_; lean_object* v_toSignature_573_; lean_object* v___x_574_; 
v_mainDecl_572_ = lean_ctor_get(v_a_473_, 1);
v_toSignature_573_ = lean_ctor_get(v_mainDecl_572_, 0);
v___x_574_ = lean_box(0);
v_inlineAttr_x3f_547_ = v___x_574_;
v_toSignature_548_ = v_toSignature_573_;
v___y_549_ = v_a_474_;
v___y_550_ = v_a_475_;
v___y_551_ = v_a_476_;
v___y_552_ = v_a_477_;
v___y_553_ = v_a_478_;
goto v___jp_546_;
}
else
{
lean_object* v_mainDecl_575_; lean_object* v_toSignature_576_; lean_object* v_inlineAttr_x3f_577_; 
v_mainDecl_575_ = lean_ctor_get(v_a_473_, 1);
v_toSignature_576_ = lean_ctor_get(v_mainDecl_575_, 0);
v_inlineAttr_x3f_577_ = lean_ctor_get(v_mainDecl_575_, 2);
v_inlineAttr_x3f_547_ = v_inlineAttr_x3f_577_;
v_toSignature_548_ = v_toSignature_576_;
v___y_549_ = v_a_474_;
v___y_550_ = v_a_475_;
v___y_551_ = v_a_476_;
v___y_552_ = v_a_477_;
v___y_553_ = v_a_478_;
goto v___jp_546_;
}
v___jp_546_:
{
uint8_t v_safe_554_; uint8_t v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_safe_554_ = lean_ctor_get_uint8(v_toSignature_548_, sizeof(void*)*4);
v___x_555_ = 0;
v___x_556_ = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1);
v___x_557_ = 0;
v___x_558_ = lean_st_mk_ref(v___x_556_);
lean_inc(v_inlineAttr_x3f_547_);
lean_inc_ref(v_decl_472_);
lean_inc_ref(v_closure_471_);
v___x_559_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_471_, v_decl_472_, v_a_545_, v_safe_554_, v_inlineAttr_x3f_547_, v___x_557_, v___x_558_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_st_ref_get(v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_561_);
v___y_490_ = v___y_552_;
v___y_491_ = v___y_553_;
v___y_492_ = v___y_551_;
v___y_493_ = v___x_555_;
v___y_494_ = v___y_549_;
v___y_495_ = v___y_550_;
v_a_496_ = v_a_560_;
goto v___jp_489_;
}
else
{
lean_dec(v___x_558_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_562_; 
v_a_562_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_559_, 1);
v___y_490_ = v___y_552_;
v___y_491_ = v___y_553_;
v___y_492_ = v___y_551_;
v___y_493_ = v___x_555_;
v___y_494_ = v___y_549_;
v___y_495_ = v___y_550_;
v_a_496_ = v_a_562_;
goto v___jp_489_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_decl_472_);
lean_dec_ref(v_closure_471_);
v_a_563_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_559_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v_decl_472_);
lean_dec_ref(v_closure_471_);
v_a_578_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_544_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_544_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
v___jp_480_:
{
size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_sz_484_ = lean_array_size(v_closure_471_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_484_, v___x_485_, v_closure_471_);
v___x_487_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_487_, 0, v_auxDeclName_482_);
lean_ctor_set(v___x_487_, 1, v___y_481_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
v___x_488_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_472_, v___x_487_, v___y_483_);
lean_dec_ref(v_decl_472_);
return v___x_488_;
}
v___jp_489_:
{
lean_object* v_toSignature_497_; lean_object* v_name_498_; lean_object* v_levelParams_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_toSignature_497_ = lean_ctor_get(v_a_496_, 0);
v_name_498_ = lean_ctor_get(v_toSignature_497_, 0);
v_levelParams_499_ = lean_ctor_get(v_toSignature_497_, 1);
v___x_500_ = lean_box(0);
lean_inc(v_levelParams_499_);
v___x_501_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(v_levelParams_499_, v___x_500_);
lean_inc_ref(v_a_496_);
v___x_502_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___y_493_, v_a_496_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
if (lean_obj_tag(v_a_503_) == 0)
{
lean_object* v___x_504_; 
lean_inc(v_name_498_);
lean_inc_ref(v_a_496_);
v___x_504_ = l_Lean_Compiler_LCNF_Decl_save(v___y_493_, v_a_496_, v___y_495_, v___y_492_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_505_; lean_object* v_decls_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref_known(v___x_504_, 1);
v___x_505_ = lean_st_ref_take(v___y_494_);
v_decls_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_505_, 1);
lean_dec(v_unused_517_);
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_decls_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_array_push(v_decls_506_, v_a_496_);
v___x_511_ = lean_unsigned_to_nat(0u);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_511_);
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_st_ref_put(v___y_494_, v___x_513_);
v___y_481_ = v___x_501_;
v_auxDeclName_482_ = v_name_498_;
v___y_483_ = v___y_492_;
goto v___jp_480_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v___x_501_);
lean_dec(v_name_498_);
lean_dec_ref(v_a_496_);
lean_dec_ref(v_decl_472_);
lean_dec_ref(v_closure_471_);
v_a_518_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_504_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_504_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_declName_526_; lean_object* v___x_527_; 
v_declName_526_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_declName_526_);
lean_dec_ref_known(v_a_503_, 1);
v___x_527_ = l_Lean_Compiler_LCNF_eraseDecl(v___y_493_, v_a_496_, v___y_495_, v___y_492_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref_known(v___x_527_, 1);
v___y_481_ = v___x_501_;
v_auxDeclName_482_ = v_declName_526_;
v___y_483_ = v___y_492_;
goto v___jp_480_;
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_declName_526_);
lean_dec(v___x_501_);
lean_dec_ref(v_decl_472_);
lean_dec_ref(v_closure_471_);
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v___x_501_);
lean_dec_ref(v_a_496_);
lean_dec_ref(v_decl_472_);
lean_dec_ref(v_closure_471_);
v_a_536_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_502_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_502_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_closure_471_ = stack[0].m_obj;
lean_object* v_decl_472_ = stack[1].m_obj;
lean_object* v_a_473_ = stack[2].m_obj;
lean_object* v_a_474_ = stack[3].m_obj;
lean_object* v_a_475_ = stack[4].m_obj;
lean_object* v_a_476_ = stack[5].m_obj;
lean_object* v_a_477_ = stack[6].m_obj;
lean_object* v_a_478_ = stack[7].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_471_, v_decl_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object* v_closure_587_, lean_object* v_decl_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_587_, v_decl_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_596_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object* v_closure_597_, lean_object* v_decl_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_597_, v_decl_598_, v_a_599_, v_a_600_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
return v___x_607_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_closure_597_ = stack[0].m_obj;
lean_object* v_decl_598_ = stack[1].m_obj;
lean_object* v_a_599_ = stack[2].m_obj;
lean_object* v_a_600_ = stack[3].m_obj;
lean_object* v_a_601_ = stack[4].m_obj;
lean_object* v_a_602_ = stack[5].m_obj;
lean_object* v_a_603_ = stack[6].m_obj;
lean_object* v_a_604_ = stack[7].m_obj;
lean_object* v_a_605_ = stack[8].m_obj;
lean_object* v_res_608_;
v_res_608_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(v_closure_597_, v_decl_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object* v_closure_609_, lean_object* v_decl_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(v_closure_609_, v_decl_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
return v_res_619_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(lean_object* v_as_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_b_625_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_625_);
return v___x_628_;
}
else
{
lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_681_; 
v_snd_629_ = lean_ctor_get(v_b_625_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_b_625_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v_b_625_, 0);
lean_dec(v_unused_682_);
v___x_631_ = v_b_625_;
v_isShared_632_ = v_isSharedCheck_681_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_dec(v_b_625_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_681_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_array_633_; lean_object* v_start_634_; lean_object* v_stop_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_array_633_ = lean_ctor_get(v_snd_629_, 0);
v_start_634_ = lean_ctor_get(v_snd_629_, 1);
v_stop_635_ = lean_ctor_get(v_snd_629_, 2);
v___x_636_ = lean_box(0);
v___x_637_ = lean_nat_dec_lt(v_start_634_, v_stop_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_636_);
v___x_639_ = v___x_631_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_snd_629_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
else
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_677_; 
lean_inc(v_stop_635_);
lean_inc(v_start_634_);
lean_inc_ref(v_array_633_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_snd_629_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_678_ = lean_ctor_get(v_snd_629_, 2);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_snd_629_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_snd_629_, 0);
lean_dec(v_unused_680_);
v___x_643_ = v_snd_629_;
v_isShared_644_ = v_isSharedCheck_677_;
goto v_resetjp_642_;
}
else
{
lean_dec(v_snd_629_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_677_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v_a_645_ = lean_array_uget(v_as_622_, v_i_624_);
v___x_646_ = lean_array_fget(v_array_633_, v_start_634_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_add(v_start_634_, v___x_647_);
lean_dec(v_start_634_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_648_);
v___x_650_ = v___x_643_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_array_633_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_stop_635_);
v___x_650_ = v_reuseFailAlloc_676_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
if (lean_obj_tag(v_a_645_) == 1)
{
lean_object* v_fvarId_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_670_; 
v_fvarId_651_ = lean_ctor_get(v_a_645_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_670_ == 0)
{
v___x_653_ = v_a_645_;
v_isShared_654_ = v_isSharedCheck_670_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_fvarId_651_);
lean_dec(v_a_645_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_670_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fvarId_655_; uint8_t v___x_656_; 
v_fvarId_655_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_fvarId_655_);
lean_dec(v___x_646_);
v___x_656_ = l_Lean_instBEqFVarId_beq(v_fvarId_651_, v_fvarId_655_);
lean_dec(v_fvarId_655_);
lean_dec(v_fvarId_651_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_650_);
lean_ctor_set(v___x_631_, 0, v___x_657_);
v___x_659_ = v___x_631_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_650_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 0, v___x_659_);
v___x_661_ = v___x_653_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v___x_665_; 
lean_del_object(v___x_653_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_650_);
lean_ctor_set(v___x_631_, 0, v___x_636_);
v___x_665_ = v___x_631_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_650_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
size_t v___x_666_; size_t v___x_667_; 
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_624_, v___x_666_);
v_i_624_ = v___x_667_;
v_b_625_ = v___x_665_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v___x_646_);
lean_dec(v_a_645_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_650_);
lean_ctor_set(v___x_631_, 0, v___x_671_);
v___x_673_ = v___x_631_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_650_);
v___x_673_ = v_reuseFailAlloc_675_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_622_ = stack[0].m_obj;
size_t v_sz_623_ = stack[1].m_num;
size_t v_i_624_ = stack[2].m_num;
lean_object* v_b_625_ = stack[3].m_obj;
lean_object* v_res_683_;
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_622_, v_sz_623_, v_i_624_, v_b_625_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(lean_object* v_as_684_, lean_object* v_sz_685_, lean_object* v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_685_);
lean_dec(v_sz_685_);
v_i_boxed_690_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_684_, v_sz_boxed_689_, v_i_boxed_690_, v_b_687_);
lean_dec_ref(v_as_684_);
return v_res_691_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(lean_object* v_decl_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_allowEtaContraction_706_; 
v_allowEtaContraction_706_ = lean_ctor_get_uint8(v_a_695_, sizeof(void*)*3 + 2);
if (v_allowEtaContraction_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref(v_decl_694_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
else
{
lean_object* v_value_709_; 
v_value_709_ = lean_ctor_get(v_decl_694_, 4);
lean_inc_ref(v_value_709_);
if (lean_obj_tag(v_value_709_) == 0)
{
lean_object* v_decl_710_; lean_object* v_value_711_; 
v_decl_710_ = lean_ctor_get(v_value_709_, 0);
lean_inc_ref(v_decl_710_);
v_value_711_ = lean_ctor_get(v_decl_710_, 3);
lean_inc(v_value_711_);
if (lean_obj_tag(v_value_711_) == 3)
{
lean_object* v_k_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_827_; 
v_k_712_ = lean_ctor_get(v_value_709_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_value_709_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_value_709_, 0);
lean_dec(v_unused_828_);
v___x_714_ = v_value_709_;
v_isShared_715_ = v_isSharedCheck_827_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_k_712_);
lean_dec(v_value_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_827_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
if (lean_obj_tag(v_k_712_) == 5)
{
lean_object* v_params_716_; lean_object* v_fvarId_717_; lean_object* v_declName_718_; lean_object* v_us_719_; lean_object* v_args_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_826_; 
v_params_716_ = lean_ctor_get(v_decl_694_, 2);
v_fvarId_717_ = lean_ctor_get(v_decl_710_, 0);
lean_inc(v_fvarId_717_);
lean_dec_ref(v_decl_710_);
v_declName_718_ = lean_ctor_get(v_value_711_, 0);
v_us_719_ = lean_ctor_get(v_value_711_, 1);
v_args_720_ = lean_ctor_get(v_value_711_, 2);
v_isSharedCheck_826_ = !lean_is_exclusive(v_value_711_);
if (v_isSharedCheck_826_ == 0)
{
v___x_722_ = v_value_711_;
v_isShared_723_ = v_isSharedCheck_826_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_args_720_);
lean_inc(v_us_719_);
lean_inc(v_declName_718_);
lean_dec(v_value_711_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_826_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_fvarId_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_825_; 
v_fvarId_724_ = lean_ctor_get(v_k_712_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_k_712_);
if (v_isSharedCheck_825_ == 0)
{
v___x_726_ = v_k_712_;
v_isShared_727_ = v_isSharedCheck_825_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_fvarId_724_);
lean_dec(v_k_712_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_825_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_instBEqFVarId_beq(v_fvarId_717_, v_fvarId_724_);
lean_dec(v_fvarId_724_);
lean_dec(v_fvarId_717_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_del_object(v___x_714_);
lean_dec_ref(v_decl_694_);
v___x_729_ = lean_box(0);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 0);
lean_ctor_set(v___x_726_, 0, v___x_729_);
v___x_731_ = v___x_726_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = lean_array_get_size(v_args_720_);
v___x_734_ = lean_array_get_size(v_params_716_);
v___x_735_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_del_object(v___x_714_);
lean_dec_ref(v_decl_694_);
v___x_736_ = lean_box(0);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 0);
lean_ctor_set(v___x_726_, 0, v___x_736_);
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v___x_740_; 
lean_del_object(v___x_726_);
v___x_740_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_698_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; uint8_t v___x_742_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = lean_unbox(v_a_741_);
lean_dec(v_a_741_);
lean_inc(v_declName_718_);
v___x_743_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_718_, v___x_742_, v_a_700_, v_a_701_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_808_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_808_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_808_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_808_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
if (lean_obj_tag(v_a_744_) == 1)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_802_; 
lean_del_object(v___x_746_);
v_isSharedCheck_802_ = !lean_is_exclusive(v_a_744_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_a_744_, 0);
lean_dec(v_unused_803_);
v___x_749_ = v_a_744_;
v_isShared_750_ = v_isSharedCheck_802_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_a_744_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_802_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_751_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_params_716_);
v___x_752_ = l_Array_toSubarray___redArg(v_params_716_, v___x_751_, v___x_734_);
v___x_753_ = lean_box(0);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_752_);
lean_ctor_set(v___x_714_, 0, v___x_753_);
v___x_755_ = v___x_714_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_752_);
v___x_755_ = v_reuseFailAlloc_801_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
size_t v_sz_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_sz_756_ = lean_array_size(v_args_720_);
v___x_757_ = ((size_t)0ULL);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_args_720_, v_sz_756_, v___x_757_, v___x_755_);
lean_dec_ref(v_args_720_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_792_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_792_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_792_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_792_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fst_763_; 
v_fst_763_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_fst_763_);
lean_dec(v_a_759_);
if (lean_obj_tag(v_fst_763_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_del_object(v___x_761_);
v___x_764_ = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0));
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 2, v___x_764_);
v___x_766_ = v___x_722_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_declName_718_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_us_719_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v___x_764_);
v___x_766_ = v_reuseFailAlloc_787_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_694_, v___x_766_, v_a_699_);
lean_dec_ref(v_decl_694_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_778_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_778_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v_a_768_);
v___x_773_ = v___x_749_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_del_object(v___x_749_);
v_a_779_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_767_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_767_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
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
else
{
lean_object* v_val_788_; lean_object* v___x_790_; 
lean_del_object(v___x_749_);
lean_del_object(v___x_722_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_dec_ref(v_decl_694_);
v_val_788_ = lean_ctor_get(v_fst_763_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_fst_763_, 1);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_val_788_);
v___x_790_ = v___x_761_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_788_);
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
lean_del_object(v___x_749_);
lean_del_object(v___x_722_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_dec_ref(v_decl_694_);
v_a_793_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_758_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_758_);
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
else
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec(v_a_744_);
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_del_object(v___x_714_);
lean_dec_ref(v_decl_694_);
v___x_804_ = lean_box(0);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_804_);
v___x_806_ = v___x_746_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_del_object(v___x_714_);
lean_dec_ref(v_decl_694_);
v_a_809_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_743_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_743_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_us_719_);
lean_dec(v_declName_718_);
lean_del_object(v___x_714_);
lean_dec_ref(v_decl_694_);
v_a_817_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_740_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_740_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
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
lean_del_object(v___x_714_);
lean_dec_ref(v_k_712_);
lean_dec_ref_known(v_value_711_, 3);
lean_dec_ref(v_decl_710_);
lean_dec_ref(v_decl_694_);
goto v___jp_703_;
}
}
}
else
{
lean_dec(v_value_711_);
lean_dec_ref_known(v_value_709_, 2);
lean_dec_ref(v_decl_710_);
lean_dec_ref(v_decl_694_);
goto v___jp_703_;
}
}
else
{
lean_dec_ref(v_value_709_);
lean_dec_ref(v_decl_694_);
goto v___jp_703_;
}
}
v___jp_703_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_694_ = stack[0].m_obj;
lean_object* v_a_695_ = stack[1].m_obj;
lean_object* v_a_696_ = stack[2].m_obj;
lean_object* v_a_697_ = stack[3].m_obj;
lean_object* v_a_698_ = stack[4].m_obj;
lean_object* v_a_699_ = stack[5].m_obj;
lean_object* v_a_700_ = stack[6].m_obj;
lean_object* v_a_701_ = stack[7].m_obj;
lean_object* v_res_829_;
v_res_829_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_decl_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(lean_object* v_decl_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_decl_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_839_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(lean_object* v_as_840_, size_t v_sz_841_, size_t v_i_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_840_, v_sz_841_, v_i_842_, v_b_843_);
return v___x_852_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_840_ = stack[0].m_obj;
size_t v_sz_841_ = stack[1].m_num;
size_t v_i_842_ = stack[2].m_num;
lean_object* v_b_843_ = stack[3].m_obj;
lean_object* v___y_844_ = stack[4].m_obj;
lean_object* v___y_845_ = stack[5].m_obj;
lean_object* v___y_846_ = stack[6].m_obj;
lean_object* v___y_847_ = stack[7].m_obj;
lean_object* v___y_848_ = stack[8].m_obj;
lean_object* v___y_849_ = stack[9].m_obj;
lean_object* v___y_850_ = stack[10].m_obj;
lean_object* v_res_853_;
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(v_as_840_, v_sz_841_, v_i_842_, v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
stack->m_obj
 = v_res_853_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(lean_object* v_as_854_, lean_object* v_sz_855_, lean_object* v_i_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
size_t v_sz_boxed_866_; size_t v_i_boxed_867_; lean_object* v_res_868_; 
v_sz_boxed_866_ = lean_unbox_usize(v_sz_855_);
lean_dec(v_sz_855_);
v_i_boxed_867_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(v_as_854_, v_sz_boxed_866_, v_i_boxed_867_, v_b_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_as_854_);
return v_res_868_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object* v_as_869_, size_t v_i_870_, size_t v_stop_871_, lean_object* v_b_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_eq(v_i_870_, v_stop_871_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v_fvarId_875_; lean_object* v___x_876_; size_t v___x_877_; size_t v___x_878_; 
v___x_874_ = lean_array_uget_borrowed(v_as_869_, v_i_870_);
v_fvarId_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_fvarId_875_);
v___x_876_ = l_Lean_FVarIdSet_insert(v_b_872_, v_fvarId_875_);
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_add(v_i_870_, v___x_877_);
v_i_870_ = v___x_878_;
v_b_872_ = v___x_876_;
goto _start;
}
else
{
return v_b_872_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_869_ = stack[0].m_obj;
size_t v_i_870_ = stack[1].m_num;
size_t v_stop_871_ = stack[2].m_num;
lean_object* v_b_872_ = stack[3].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_as_869_, v_i_870_, v_stop_871_, v_b_872_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object* v_as_881_, lean_object* v_i_882_, lean_object* v_stop_883_, lean_object* v_b_884_){
_start:
{
size_t v_i_boxed_885_; size_t v_stop_boxed_886_; lean_object* v_res_887_; 
v_i_boxed_885_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_stop_boxed_886_ = lean_unbox_usize(v_stop_883_);
lean_dec(v_stop_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_as_881_, v_i_boxed_885_, v_stop_boxed_886_, v_b_884_);
lean_dec_ref(v_as_881_);
return v_res_887_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(lean_object* v_k_888_, lean_object* v_t_889_){
_start:
{
if (lean_obj_tag(v_t_889_) == 0)
{
lean_object* v_k_890_; lean_object* v_l_891_; lean_object* v_r_892_; uint8_t v___x_893_; 
v_k_890_ = lean_ctor_get(v_t_889_, 1);
v_l_891_ = lean_ctor_get(v_t_889_, 3);
v_r_892_ = lean_ctor_get(v_t_889_, 4);
v___x_893_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_888_, v_k_890_);
switch(v___x_893_)
{
case 0:
{
v_t_889_ = v_l_891_;
goto _start;
}
case 1:
{
uint8_t v___x_895_; 
v___x_895_ = 1;
return v___x_895_;
}
default: 
{
v_t_889_ = v_r_892_;
goto _start;
}
}
}
else
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_888_ = stack[0].m_obj;
lean_object* v_t_889_ = stack[1].m_obj;
uint8_t v_res_898_;
v_res_898_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_888_, v_t_889_);
stack->m_num = v_res_898_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(lean_object* v_k_899_, lean_object* v_t_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_899_, v_t_900_);
lean_dec(v_t_900_);
lean_dec(v_k_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object* v_a_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v___y_904_, v_a_903_);
return v___x_905_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_903_ = stack[0].m_obj;
lean_object* v___y_904_ = stack[1].m_obj;
uint8_t v_res_906_;
v_res_906_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(v_a_903_, v___y_904_);
stack->m_num = v_res_906_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object* v_a_907_, lean_object* v___y_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(v_a_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec(v_a_907_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t v_a_911_, lean_object* v_x_912_){
_start:
{
return v_a_911_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_911_ = stack[0].m_num;
lean_object* v_x_912_ = stack[1].m_obj;
uint8_t v_res_913_;
v_res_913_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(v_a_911_, v_x_912_);
stack->m_num = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object* v_a_914_, lean_object* v_x_915_){
_start:
{
uint8_t v_a_12998__boxed_916_; uint8_t v_res_917_; lean_object* v_r_918_; 
v_a_12998__boxed_916_ = lean_unbox(v_a_914_);
v_res_917_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(v_a_12998__boxed_916_, v_x_915_);
lean_dec(v_x_915_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(lean_object* v_i_919_, lean_object* v_as_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_array_get_size(v_as_920_);
v___x_930_ = lean_nat_dec_lt(v_i_919_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_i_919_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_as_920_);
return v___x_931_;
}
else
{
lean_object* v_a_932_; lean_object* v_a_934_; 
v_a_932_ = lean_array_fget_borrowed(v_as_920_, v_i_919_);
if (lean_obj_tag(v_a_932_) == 0)
{
lean_object* v_params_945_; lean_object* v_code_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_params_945_ = lean_ctor_get(v_a_932_, 1);
v_code_946_ = lean_ctor_get(v_a_932_, 2);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_array_get_size(v_params_945_);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_inc_ref(v_code_946_);
v___x_950_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_946_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
lean_inc_ref(v_a_932_);
v___x_952_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_932_, v_a_951_);
v_a_934_ = v___x_952_;
goto v___jp_933_;
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v_as_920_);
lean_dec(v_i_919_);
v_a_953_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_950_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = ((size_t)0ULL);
v___x_962_ = lean_usize_of_nat(v___x_948_);
lean_inc(v___y_923_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_945_, v___x_961_, v___x_962_, v___y_923_);
lean_inc_ref(v_code_946_);
v___x_964_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_946_, v___y_921_, v___y_922_, v___x_963_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___x_963_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
lean_inc_ref(v_a_932_);
v___x_966_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_932_, v_a_965_);
v_a_934_ = v___x_966_;
goto v___jp_933_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_as_920_);
lean_dec(v_i_919_);
v_a_967_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_964_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v_code_975_; lean_object* v___x_976_; 
v_code_975_ = lean_ctor_get(v_a_932_, 0);
lean_inc_ref(v_code_975_);
v___x_976_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_975_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
lean_inc_ref(v_a_932_);
v___x_978_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_932_, v_a_977_);
v_a_934_ = v___x_978_;
goto v___jp_933_;
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v_as_920_);
lean_dec(v_i_919_);
v_a_979_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_976_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
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
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_ptr_addr(v_a_932_);
v___x_936_ = lean_ptr_addr(v_a_934_);
v___x_937_ = lean_usize_dec_eq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_add(v_i_919_, v___x_938_);
v___x_940_ = lean_array_fset(v_as_920_, v_i_919_, v_a_934_);
lean_dec(v_i_919_);
v_i_919_ = v___x_939_;
v_as_920_ = v___x_940_;
goto _start;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec_ref(v_a_934_);
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_i_919_, v___x_942_);
lean_dec(v_i_919_);
v_i_919_ = v___x_943_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_919_ = stack[0].m_obj;
lean_object* v_as_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v___y_925_ = stack[6].m_obj;
lean_object* v___y_926_ = stack[7].m_obj;
lean_object* v___y_927_ = stack[8].m_obj;
lean_object* v_res_987_;
v_res_987_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v_i_919_, v_as_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
stack->m_obj
 = v_res_987_;
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object* v_code_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
switch(lean_obj_tag(v_code_988_))
{
case 0:
{
lean_object* v_decl_997_; lean_object* v_k_998_; lean_object* v_fvarId_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_decl_997_ = lean_ctor_get(v_code_988_, 0);
v_k_998_ = lean_ctor_get(v_code_988_, 1);
v_fvarId_999_ = lean_ctor_get(v_decl_997_, 0);
lean_inc(v_fvarId_999_);
lean_inc(v_a_991_);
v___x_1000_ = l_Lean_FVarIdSet_insert(v_a_991_, v_fvarId_999_);
lean_inc_ref(v_k_998_);
v___x_1001_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_998_, v_a_989_, v_a_990_, v___x_1000_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v___x_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1038_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1038_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1038_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
size_t v___x_1006_; size_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_ptr_addr(v_k_998_);
v___x_1007_ = lean_ptr_addr(v_a_1002_);
v___x_1008_ = lean_usize_dec_eq(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1018_; 
lean_inc_ref(v_decl_997_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; lean_object* v_unused_1020_; 
v_unused_1019_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1020_);
v___x_1010_ = v_code_988_;
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
else
{
lean_dec(v_code_988_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v_a_1002_);
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_decl_997_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_a_1002_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1013_);
v___x_1015_ = v___x_1004_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
size_t v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_ptr_addr(v_decl_997_);
v___x_1022_ = lean_usize_dec_eq(v___x_1021_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1032_; 
lean_inc_ref(v_decl_997_);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; lean_object* v_unused_1034_; 
v_unused_1033_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1034_);
v___x_1024_ = v_code_988_;
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v_code_988_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_a_1002_);
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_decl_997_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1002_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1027_);
v___x_1029_ = v___x_1004_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_a_1002_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_code_988_);
v___x_1036_ = v___x_1004_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_code_988_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_988_, 2);
return v___x_1001_;
}
}
case 1:
{
lean_object* v_decl_1039_; lean_object* v_k_1040_; lean_object* v_declNew_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___f_1062_; lean_object* v___x_1063_; 
v_decl_1039_ = lean_ctor_get(v_code_988_, 0);
v_k_1040_ = lean_ctor_get(v_code_988_, 1);
lean_inc(v_a_991_);
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1062_, 0, v_a_991_);
lean_inc_ref(v_decl_1039_);
v___x_1063_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_decl_1039_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_a_1064_, v_a_989_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; uint8_t v___x_1067_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = lean_unbox(v_a_1066_);
if (v___x_1067_ == 0)
{
lean_object* v_fvarId_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v_a_1066_);
lean_dec_ref(v___f_1062_);
v_fvarId_1068_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fvarId_1068_);
lean_inc(v_a_991_);
v___x_1069_ = l_Lean_FVarIdSet_insert(v_a_991_, v_fvarId_1068_);
lean_inc_ref(v_k_1040_);
v___x_1070_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1040_, v_a_989_, v_a_990_, v___x_1069_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v___x_1069_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1108_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1108_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1108_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
size_t v___x_1075_; size_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_ptr_addr(v_k_1040_);
v___x_1076_ = lean_ptr_addr(v_a_1071_);
v___x_1077_ = lean_usize_dec_eq(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1087_; 
v_isSharedCheck_1087_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; lean_object* v_unused_1089_; 
v_unused_1088_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1089_);
v___x_1079_ = v_code_988_;
v_isShared_1080_ = v_isSharedCheck_1087_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v_code_988_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1087_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_a_1071_);
lean_ctor_set(v___x_1079_, 0, v_a_1064_);
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1064_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_a_1071_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1082_);
v___x_1084_ = v___x_1073_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
size_t v___x_1090_; size_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = lean_ptr_addr(v_decl_1039_);
v___x_1091_ = lean_ptr_addr(v_a_1064_);
v___x_1092_ = lean_usize_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_isSharedCheck_1102_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; 
v_unused_1103_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1104_);
v___x_1094_ = v_code_988_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v_code_988_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_a_1071_);
lean_ctor_set(v___x_1094_, 0, v_a_1064_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1064_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_a_1071_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1097_);
v___x_1099_ = v___x_1073_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_a_1071_);
lean_dec(v_a_1064_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v_code_988_);
v___x_1106_ = v___x_1073_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_code_988_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
else
{
lean_dec(v_a_1064_);
lean_dec_ref_known(v_code_988_, 2);
return v___x_1070_;
}
}
else
{
lean_object* v___f_1109_; lean_object* v___x_1110_; 
lean_inc_ref(v_k_1040_);
lean_dec_ref_known(v_code_988_, 2);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1109_, 0, v_a_1066_);
lean_inc(v_a_1064_);
v___x_1110_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_a_1064_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
if (lean_obj_tag(v_a_1111_) == 1)
{
lean_object* v_val_1112_; 
lean_dec_ref(v___f_1109_);
lean_dec(v_a_1064_);
lean_dec_ref(v___f_1062_);
v_val_1112_ = lean_ctor_get(v_a_1111_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v_a_1111_, 1);
v_declNew_1042_ = v_val_1112_;
v___y_1043_ = v_a_989_;
v___y_1044_ = v_a_990_;
v___y_1045_ = v_a_991_;
v___y_1046_ = v_a_992_;
v___y_1047_ = v_a_993_;
v___y_1048_ = v_a_994_;
v___y_1049_ = v_a_995_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_a_1111_);
lean_inc(v_a_1064_);
v___x_1113_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed), 8, 1);
lean_closure_set(v___x_1113_, 0, v_a_1064_);
v___x_1114_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v___x_1113_, v___f_1062_, v___f_1109_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v_snd_1116_; lean_object* v_fst_1117_; lean_object* v___x_1118_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v_snd_1116_ = lean_ctor_get(v_a_1115_, 1);
lean_inc(v_snd_1116_);
lean_dec(v_a_1115_);
v_fst_1117_ = lean_ctor_get(v_snd_1116_, 0);
lean_inc(v_fst_1117_);
lean_dec(v_snd_1116_);
v___x_1118_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_fst_1117_, v_a_1064_, v_a_989_, v_a_990_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v_declNew_1042_ = v_a_1119_;
v___y_1043_ = v_a_989_;
v___y_1044_ = v_a_990_;
v___y_1045_ = v_a_991_;
v___y_1046_ = v_a_992_;
v___y_1047_ = v_a_993_;
v___y_1048_ = v_a_994_;
v___y_1049_ = v_a_995_;
goto v___jp_1041_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_k_1040_);
v_a_1120_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_a_1064_);
lean_dec_ref(v_k_1040_);
v_a_1128_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1114_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1114_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v___f_1109_);
lean_dec(v_a_1064_);
lean_dec_ref(v___f_1062_);
lean_dec_ref(v_k_1040_);
v_a_1136_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1110_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1110_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_1064_);
lean_dec_ref(v___f_1062_);
lean_dec_ref_known(v_code_988_, 2);
v_a_1144_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1065_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1065_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
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
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___f_1062_);
lean_dec_ref_known(v_code_988_, 2);
v_a_1152_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1063_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1063_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
v___jp_1041_:
{
lean_object* v_fvarId_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_fvarId_1050_ = lean_ctor_get(v_declNew_1042_, 0);
lean_inc(v_fvarId_1050_);
lean_inc(v___y_1045_);
v___x_1051_ = l_Lean_FVarIdSet_insert(v___y_1045_, v_fvarId_1050_);
v___x_1052_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1040_, v___y_1043_, v___y_1044_, v___x_1051_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_declNew_1042_);
lean_ctor_set(v___x_1057_, 1, v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_dec_ref(v_declNew_1042_);
return v___x_1052_;
}
}
}
case 2:
{
lean_object* v_decl_1160_; lean_object* v_k_1161_; lean_object* v___x_1162_; 
v_decl_1160_ = lean_ctor_get(v_code_988_, 0);
v_k_1161_ = lean_ctor_get(v_code_988_, 1);
lean_inc_ref(v_decl_1160_);
v___x_1162_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_decl_1160_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_fvarId_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_fvarId_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_fvarId_1164_);
lean_inc(v_a_991_);
v___x_1165_ = l_Lean_FVarIdSet_insert(v_a_991_, v_fvarId_1164_);
lean_inc_ref(v_k_1161_);
v___x_1166_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1161_, v_a_989_, v_a_990_, v___x_1165_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v___x_1165_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1204_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1204_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1204_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
size_t v___x_1171_; size_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_ptr_addr(v_k_1161_);
v___x_1172_ = lean_ptr_addr(v_a_1167_);
v___x_1173_ = lean_usize_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1183_; 
v_isSharedCheck_1183_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1184_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1185_);
v___x_1175_ = v_code_988_;
v_isShared_1176_ = v_isSharedCheck_1183_;
goto v_resetjp_1174_;
}
else
{
lean_dec(v_code_988_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1183_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_a_1167_);
lean_ctor_set(v___x_1175_, 0, v_a_1163_);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_a_1167_);
v___x_1178_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1178_);
v___x_1180_ = v___x_1169_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
size_t v___x_1186_; size_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_ptr_addr(v_decl_1160_);
v___x_1187_ = lean_ptr_addr(v_a_1163_);
v___x_1188_ = lean_usize_dec_eq(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1199_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1200_);
v___x_1190_ = v_code_988_;
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_code_988_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_a_1167_);
lean_ctor_set(v___x_1190_, 0, v_a_1163_);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_a_1167_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1193_);
v___x_1195_ = v___x_1169_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v_a_1167_);
lean_dec(v_a_1163_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_code_988_);
v___x_1202_ = v___x_1169_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_code_988_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_dec(v_a_1163_);
lean_dec_ref_known(v_code_988_, 2);
return v___x_1166_;
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref_known(v_code_988_, 2);
v_a_1205_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1162_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1162_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
case 4:
{
lean_object* v_cases_1213_; lean_object* v_typeName_1214_; lean_object* v_resultType_1215_; lean_object* v_discr_1216_; lean_object* v_alts_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1256_; 
v_cases_1213_ = lean_ctor_get(v_code_988_, 0);
lean_inc_ref(v_cases_1213_);
v_typeName_1214_ = lean_ctor_get(v_cases_1213_, 0);
v_resultType_1215_ = lean_ctor_get(v_cases_1213_, 1);
v_discr_1216_ = lean_ctor_get(v_cases_1213_, 2);
v_alts_1217_ = lean_ctor_get(v_cases_1213_, 3);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_cases_1213_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1219_ = v_cases_1213_;
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_alts_1217_);
lean_inc(v_discr_1216_);
lean_inc(v_resultType_1215_);
lean_inc(v_typeName_1214_);
lean_dec(v_cases_1213_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1217_);
v___x_1222_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v___x_1221_, v_alts_1217_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1247_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1247_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1247_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
size_t v___x_1227_; size_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = lean_ptr_addr(v_alts_1217_);
lean_dec_ref(v_alts_1217_);
v___x_1228_ = lean_ptr_addr(v_a_1223_);
v___x_1229_ = lean_usize_dec_eq(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1242_; 
v_isSharedCheck_1242_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1243_);
v___x_1231_ = v_code_988_;
v_isShared_1232_ = v_isSharedCheck_1242_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v_code_988_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1242_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 3, v_a_1223_);
v___x_1234_ = v___x_1219_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_typeName_1214_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_resultType_1215_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_discr_1216_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_a_1223_);
v___x_1234_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1238_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1236_);
v___x_1238_ = v___x_1225_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_a_1223_);
lean_del_object(v___x_1219_);
lean_dec(v_discr_1216_);
lean_dec_ref(v_resultType_1215_);
lean_dec(v_typeName_1214_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_code_988_);
v___x_1245_ = v___x_1225_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_code_988_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_del_object(v___x_1219_);
lean_dec_ref(v_alts_1217_);
lean_dec(v_discr_1216_);
lean_dec_ref(v_resultType_1215_);
lean_dec(v_typeName_1214_);
lean_dec_ref_known(v_code_988_, 1);
v_a_1248_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1222_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1222_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
default: 
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_code_988_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_visitCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_988_ = stack[0].m_obj;
lean_object* v_a_989_ = stack[1].m_obj;
lean_object* v_a_990_ = stack[2].m_obj;
lean_object* v_a_991_ = stack[3].m_obj;
lean_object* v_a_992_ = stack[4].m_obj;
lean_object* v_a_993_ = stack[5].m_obj;
lean_object* v_a_994_ = stack[6].m_obj;
lean_object* v_a_995_ = stack[7].m_obj;
lean_object* v_res_1258_;
v_res_1258_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
stack->m_obj
 = v_res_1258_;
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object* v_funDecl_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_params_1268_; lean_object* v_type_1269_; lean_object* v_value_1270_; uint8_t v___x_1271_; lean_object* v___y_1273_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_params_1268_ = lean_ctor_get(v_funDecl_1259_, 2);
lean_inc_ref(v_params_1268_);
v_type_1269_ = lean_ctor_get(v_funDecl_1259_, 3);
lean_inc_ref(v_type_1269_);
v_value_1270_ = lean_ctor_get(v_funDecl_1259_, 4);
v___x_1271_ = 0;
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_array_get_size(v_params_1268_);
v___x_1286_ = lean_nat_dec_lt(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_inc_ref(v_value_1270_);
v___x_1287_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1270_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
v___y_1273_ = v___x_1287_;
goto v___jp_1272_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1285_);
lean_inc(v_a_1262_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1268_, v___x_1288_, v___x_1289_, v_a_1262_);
lean_inc_ref(v_value_1270_);
v___x_1291_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1270_, v_a_1260_, v_a_1261_, v___x_1290_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
lean_dec(v___x_1290_);
v___y_1273_ = v___x_1291_;
goto v___jp_1272_;
}
v___jp_1272_:
{
if (lean_obj_tag(v___y_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___y_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___y_1273_, 1);
v___x_1275_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1271_, v_funDecl_1259_, v_type_1269_, v_params_1268_, v_a_1274_, v_a_1264_);
return v___x_1275_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_type_1269_);
lean_dec_ref(v_params_1268_);
lean_dec_ref(v_funDecl_1259_);
v_a_1276_ = lean_ctor_get(v___y_1273_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___y_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___y_1273_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___y_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_funDecl_1259_ = stack[0].m_obj;
lean_object* v_a_1260_ = stack[1].m_obj;
lean_object* v_a_1261_ = stack[2].m_obj;
lean_object* v_a_1262_ = stack[3].m_obj;
lean_object* v_a_1263_ = stack[4].m_obj;
lean_object* v_a_1264_ = stack[5].m_obj;
lean_object* v_a_1265_ = stack[6].m_obj;
lean_object* v_a_1266_ = stack[7].m_obj;
lean_object* v_res_1292_;
v_res_1292_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_funDecl_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
stack->m_obj
 = v_res_1292_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl___boxed(lean_object* v_funDecl_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_funDecl_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3___boxed(lean_object* v_i_1303_, lean_object* v_as_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v_i_1303_, v_as_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed(lean_object* v_code_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1323_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(lean_object* v_00_u03b2_1324_, lean_object* v_k_1325_, lean_object* v_t_1326_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_1325_, v_t_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1325_ = stack[1].m_obj;
lean_object* v_t_1326_ = stack[2].m_obj;
uint8_t v_res_1328_;
v_res_1328_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(lean_box(0), v_k_1325_, v_t_1326_);
stack->m_num = v_res_1328_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___boxed(lean_object* v_00_u03b2_1329_, lean_object* v_k_1330_, lean_object* v_t_1331_){
_start:
{
uint8_t v_res_1332_; lean_object* v_r_1333_; 
v_res_1332_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(v_00_u03b2_1329_, v_k_1330_, v_t_1331_);
lean_dec(v_t_1331_);
lean_dec(v_k_1330_);
v_r_1333_ = lean_box(v_res_1332_);
return v_r_1333_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(lean_object* v_f_1334_, lean_object* v_v_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
if (lean_obj_tag(v_v_1335_) == 0)
{
lean_object* v_code_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1368_; 
v_code_1344_ = lean_ctor_get(v_v_1335_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_v_1335_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1346_ = v_v_1335_;
v_isShared_1347_ = v_isSharedCheck_1368_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_code_1344_);
lean_dec(v_v_1335_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1368_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; 
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
v___x_1348_ = lean_apply_9(v_f_1334_, v_code_1344_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_a_1349_);
v___x_1354_ = v___x_1346_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_del_object(v___x_1346_);
v_a_1360_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1348_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1348_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
else
{
lean_object* v___x_1369_; 
lean_dec_ref(v_f_1334_);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v_v_1335_);
return v___x_1369_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1334_ = stack[0].m_obj;
lean_object* v_v_1335_ = stack[1].m_obj;
lean_object* v___y_1336_ = stack[2].m_obj;
lean_object* v___y_1337_ = stack[3].m_obj;
lean_object* v___y_1338_ = stack[4].m_obj;
lean_object* v___y_1339_ = stack[5].m_obj;
lean_object* v___y_1340_ = stack[6].m_obj;
lean_object* v___y_1341_ = stack[7].m_obj;
lean_object* v___y_1342_ = stack[8].m_obj;
lean_object* v_res_1370_;
v_res_1370_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1334_, v_v_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
stack->m_obj
 = v_res_1370_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg___boxed(lean_object* v_f_1371_, lean_object* v_v_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1371_, v_v_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1381_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(uint8_t v_pu_1382_, lean_object* v_f_1383_, lean_object* v_v_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1383_, v_v_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1382_ = stack[0].m_num;
lean_object* v_f_1383_ = stack[1].m_obj;
lean_object* v_v_1384_ = stack[2].m_obj;
lean_object* v___y_1385_ = stack[3].m_obj;
lean_object* v___y_1386_ = stack[4].m_obj;
lean_object* v___y_1387_ = stack[5].m_obj;
lean_object* v___y_1388_ = stack[6].m_obj;
lean_object* v___y_1389_ = stack[7].m_obj;
lean_object* v___y_1390_ = stack[8].m_obj;
lean_object* v___y_1391_ = stack[9].m_obj;
lean_object* v_res_1394_;
v_res_1394_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(v_pu_1382_, v_f_1383_, v_v_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
stack->m_obj
 = v_res_1394_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___boxed(lean_object* v_pu_1395_, lean_object* v_f_1396_, lean_object* v_v_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v_pu_boxed_1406_; lean_object* v_res_1407_; 
v_pu_boxed_1406_ = lean_unbox(v_pu_1395_);
v_res_1407_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(v_pu_boxed_1406_, v_f_1396_, v_v_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
return v_res_1407_;
}
}
lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object* v_decl_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_toSignature_1418_; lean_object* v_value_1419_; uint8_t v_recursive_1420_; lean_object* v_inlineAttr_x3f_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1456_; 
v_toSignature_1418_ = lean_ctor_get(v_decl_1409_, 0);
v_value_1419_ = lean_ctor_get(v_decl_1409_, 1);
v_recursive_1420_ = lean_ctor_get_uint8(v_decl_1409_, sizeof(void*)*3);
v_inlineAttr_x3f_1421_ = lean_ctor_get(v_decl_1409_, 2);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_decl_1409_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1423_ = v_decl_1409_;
v_isShared_1424_ = v_isSharedCheck_1456_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_inlineAttr_x3f_1421_);
lean_inc(v_value_1419_);
lean_inc(v_toSignature_1418_);
lean_dec(v_decl_1409_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1456_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___y_1426_; lean_object* v_params_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_params_1446_ = lean_ctor_get(v_toSignature_1418_, 3);
v___x_1447_ = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0));
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_array_get_size(v_params_1446_);
v___x_1450_ = lean_nat_dec_lt(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1447_, v_value_1419_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
v___y_1426_ = v___x_1451_;
goto v___jp_1425_;
}
else
{
size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = lean_usize_of_nat(v___x_1449_);
lean_inc(v_a_1412_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1446_, v___x_1452_, v___x_1453_, v_a_1412_);
v___x_1455_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1447_, v_value_1419_, v_a_1410_, v_a_1411_, v___x_1454_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v___x_1454_);
v___y_1426_ = v___x_1455_;
goto v___jp_1425_;
}
v___jp_1425_:
{
if (lean_obj_tag(v___y_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1437_; 
v_a_1427_ = lean_ctor_get(v___y_1426_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___y_1426_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1429_ = v___y_1426_;
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___y_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_a_1427_);
v___x_1432_ = v___x_1423_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_toSignature_1418_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_inlineAttr_x3f_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, sizeof(void*)*3, v_recursive_1420_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1423_);
lean_dec(v_inlineAttr_x3f_1421_);
lean_dec_ref(v_toSignature_1418_);
v_a_1438_ = lean_ctor_get(v___y_1426_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___y_1426_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___y_1426_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___y_1426_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LambdaLifting_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1409_ = stack[0].m_obj;
lean_object* v_a_1410_ = stack[1].m_obj;
lean_object* v_a_1411_ = stack[2].m_obj;
lean_object* v_a_1412_ = stack[3].m_obj;
lean_object* v_a_1413_ = stack[4].m_obj;
lean_object* v_a_1414_ = stack[5].m_obj;
lean_object* v_a_1415_ = stack[6].m_obj;
lean_object* v_a_1416_ = stack[7].m_obj;
lean_object* v_res_1457_;
v_res_1457_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
stack->m_obj
 = v_res_1457_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___boxed(lean_object* v_decl_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
return v_res_1467_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object* v_decl_1473_, uint8_t v_liftInstParamOnly_1474_, uint8_t v_allowEtaContraction_1475_, lean_object* v_suffix_1476_, uint8_t v_inheritInlineAttrs_1477_, lean_object* v_minSize_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v_ctx_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1484_ = lean_box(1);
lean_inc_ref(v_decl_1473_);
v_ctx_1485_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ctx_1485_, 0, v_suffix_1476_);
lean_ctor_set(v_ctx_1485_, 1, v_decl_1473_);
lean_ctor_set(v_ctx_1485_, 2, v_minSize_1478_);
lean_ctor_set_uint8(v_ctx_1485_, sizeof(void*)*3, v_liftInstParamOnly_1474_);
lean_ctor_set_uint8(v_ctx_1485_, sizeof(void*)*3 + 1, v_inheritInlineAttrs_1477_);
lean_ctor_set_uint8(v_ctx_1485_, sizeof(void*)*3 + 2, v_allowEtaContraction_1475_);
v___x_1486_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1));
v___x_1487_ = lean_st_mk_ref(v___x_1486_);
v___x_1488_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1473_, v_ctx_1485_, v___x_1487_, v___x_1484_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
lean_dec_ref_known(v_ctx_1485_, 3);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1499_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v_decls_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1493_ = lean_st_ref_get(v___x_1487_);
lean_dec(v___x_1487_);
v_decls_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_decls_1494_);
lean_dec(v___x_1493_);
v___x_1495_ = lean_array_push(v_decls_1494_, v_a_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1497_ = v___x_1491_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v___x_1487_);
v_a_1500_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1488_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1488_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_lambdaLifting_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1473_ = stack[0].m_obj;
uint8_t v_liftInstParamOnly_1474_ = stack[1].m_num;
uint8_t v_allowEtaContraction_1475_ = stack[2].m_num;
lean_object* v_suffix_1476_ = stack[3].m_obj;
uint8_t v_inheritInlineAttrs_1477_ = stack[4].m_num;
lean_object* v_minSize_1478_ = stack[5].m_obj;
lean_object* v_a_1479_ = stack[6].m_obj;
lean_object* v_a_1480_ = stack[7].m_obj;
lean_object* v_a_1481_ = stack[8].m_obj;
lean_object* v_a_1482_ = stack[9].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v_decl_1473_, v_liftInstParamOnly_1474_, v_allowEtaContraction_1475_, v_suffix_1476_, v_inheritInlineAttrs_1477_, v_minSize_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object* v_decl_1509_, lean_object* v_liftInstParamOnly_1510_, lean_object* v_allowEtaContraction_1511_, lean_object* v_suffix_1512_, lean_object* v_inheritInlineAttrs_1513_, lean_object* v_minSize_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
uint8_t v_liftInstParamOnly_boxed_1520_; uint8_t v_allowEtaContraction_boxed_1521_; uint8_t v_inheritInlineAttrs_boxed_1522_; lean_object* v_res_1523_; 
v_liftInstParamOnly_boxed_1520_ = lean_unbox(v_liftInstParamOnly_1510_);
v_allowEtaContraction_boxed_1521_ = lean_unbox(v_allowEtaContraction_1511_);
v_inheritInlineAttrs_boxed_1522_ = lean_unbox(v_inheritInlineAttrs_1513_);
v_res_1523_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v_decl_1509_, v_liftInstParamOnly_boxed_1520_, v_allowEtaContraction_boxed_1521_, v_suffix_1512_, v_inheritInlineAttrs_boxed_1522_, v_minSize_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1523_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(lean_object* v_as_1527_, size_t v_i_1528_, size_t v_stop_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_a_1537_; uint8_t v___x_1541_; 
v___x_1541_ = lean_usize_dec_eq(v_i_1528_, v_stop_1529_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_array_uget_borrowed(v_as_1527_, v_i_1528_);
v___x_1544_ = 1;
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1));
lean_inc(v___x_1543_);
v___x_1546_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v___x_1543_, v___x_1541_, v___x_1544_, v___x_1545_, v___x_1541_, v___x_1542_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = l_Array_append___redArg(v_b_1530_, v_a_1547_);
lean_dec(v_a_1547_);
v_a_1537_ = v___x_1548_;
goto v___jp_1536_;
}
else
{
lean_dec_ref(v_b_1530_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1549_; 
v_a_1549_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1546_, 1);
v_a_1537_ = v_a_1549_;
goto v___jp_1536_;
}
else
{
return v___x_1546_;
}
}
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_b_1530_);
return v___x_1550_;
}
v___jp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1528_, v___x_1538_);
v_i_1528_ = v___x_1539_;
v_b_1530_ = v_a_1537_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1527_ = stack[0].m_obj;
size_t v_i_1528_ = stack[1].m_num;
size_t v_stop_1529_ = stack[2].m_num;
lean_object* v_b_1530_ = stack[3].m_obj;
lean_object* v___y_1531_ = stack[4].m_obj;
lean_object* v___y_1532_ = stack[5].m_obj;
lean_object* v___y_1533_ = stack[6].m_obj;
lean_object* v___y_1534_ = stack[7].m_obj;
lean_object* v_res_1551_;
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_as_1527_, v_i_1528_, v_stop_1529_, v_b_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
stack->m_obj
 = v_res_1551_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object* v_as_1552_, lean_object* v_i_1553_, lean_object* v_stop_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
size_t v_i_boxed_1561_; size_t v_stop_boxed_1562_; lean_object* v_res_1563_; 
v_i_boxed_1561_ = lean_unbox_usize(v_i_1553_);
lean_dec(v_i_1553_);
v_stop_boxed_1562_ = lean_unbox_usize(v_stop_1554_);
lean_dec(v_stop_1554_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_as_1552_, v_i_boxed_1561_, v_stop_boxed_1562_, v_b_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v_as_1552_);
return v_res_1563_;
}
}
lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object* v___x_1564_, lean_object* v_decls_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = lean_mk_empty_array_with_capacity(v___x_1564_);
v___x_1572_ = lean_array_get_size(v_decls_1565_);
v___x_1573_ = lean_nat_dec_lt(v___x_1564_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
return v___x_1574_;
}
else
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_nat_dec_le(v___x_1572_, v___x_1572_);
if (v___x_1575_ == 0)
{
if (v___x_1573_ == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1571_);
return v___x_1576_;
}
else
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = lean_usize_of_nat(v___x_1572_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_1565_, v___x_1577_, v___x_1578_, v___x_1571_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1579_;
}
}
else
{
size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1572_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_1565_, v___x_1580_, v___x_1581_, v___x_1571_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_lambdaLifting___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1564_ = stack[0].m_obj;
lean_object* v_decls_1565_ = stack[1].m_obj;
lean_object* v___y_1566_ = stack[2].m_obj;
lean_object* v___y_1567_ = stack[3].m_obj;
lean_object* v___y_1568_ = stack[4].m_obj;
lean_object* v___y_1569_ = stack[5].m_obj;
lean_object* v_res_1583_;
v_res_1583_ = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(v___x_1564_, v_decls_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
stack->m_obj
 = v_res_1583_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object* v___x_1584_, lean_object* v_decls_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(v___x_1584_, v_decls_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v_decls_1585_);
lean_dec(v___x_1584_);
return v_res_1591_;
}
}
lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object* v_declName_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v_env_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1607_ = lean_st_ref_get(v___y_1605_);
v_env_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1608_);
lean_dec(v___x_1607_);
v___x_1609_ = l_Lean_isInstanceReducibleCore(v_env_1608_, v_declName_1604_);
v___x_1610_ = lean_box(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT void l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1604_ = stack[0].m_obj;
lean_object* v___y_1605_ = stack[1].m_obj;
lean_object* v_res_1612_;
v_res_1612_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1604_, v___y_1605_);
stack->m_obj
 = v_res_1612_;
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object* v_declName_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1613_, v___y_1614_);
lean_dec(v___y_1614_);
return v_res_1616_;
}
}
lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object* v_declName_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1617_, v___y_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT void l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1617_ = stack[0].m_obj;
lean_object* v___y_1618_ = stack[1].m_obj;
lean_object* v___y_1619_ = stack[2].m_obj;
lean_object* v___y_1620_ = stack[3].m_obj;
lean_object* v___y_1621_ = stack[4].m_obj;
lean_object* v_res_1624_;
v_res_1624_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(v_declName_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
stack->m_obj
 = v_res_1624_;
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object* v_declName_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(v_declName_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1631_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(lean_object* v_as_1635_, size_t v_i_1636_, size_t v_stop_1637_, lean_object* v_b_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_a_1645_; uint8_t v___x_1649_; 
v___x_1649_ = lean_usize_dec_eq(v_i_1636_, v_stop_1637_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v_toSignature_1651_; lean_object* v_name_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1650_ = lean_array_uget_borrowed(v_as_1635_, v_i_1636_);
v_toSignature_1651_ = lean_ctor_get(v___x_1650_, 0);
v_name_1652_ = lean_ctor_get(v_toSignature_1651_, 0);
v___x_1653_ = lean_unsigned_to_nat(0u);
lean_inc(v_name_1652_);
v___x_1654_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_name_1652_, v___y_1642_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; uint8_t v___y_1657_; uint8_t v___x_1665_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1665_ = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(v___x_1650_);
if (v___x_1665_ == 0)
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_unbox(v_a_1655_);
lean_dec(v_a_1655_);
v___y_1657_ = v___x_1666_;
goto v___jp_1656_;
}
else
{
lean_dec(v_a_1655_);
v___y_1657_ = v___x_1665_;
goto v___jp_1656_;
}
v___jp_1656_:
{
if (v___y_1657_ == 0)
{
uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = 1;
v___x_1659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1));
lean_inc(v___x_1650_);
v___x_1660_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v___x_1650_, v___x_1658_, v___x_1649_, v___x_1659_, v___x_1649_, v___x_1653_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = l_Array_append___redArg(v_b_1638_, v_a_1661_);
lean_dec(v_a_1661_);
v_a_1645_ = v___x_1662_;
goto v___jp_1644_;
}
else
{
lean_dec_ref(v_b_1638_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1663_; 
v_a_1663_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1660_, 1);
v_a_1645_ = v_a_1663_;
goto v___jp_1644_;
}
else
{
return v___x_1660_;
}
}
}
else
{
lean_object* v___x_1664_; 
lean_inc(v___x_1650_);
v___x_1664_ = lean_array_push(v_b_1638_, v___x_1650_);
v_a_1645_ = v___x_1664_;
goto v___jp_1644_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_b_1638_);
v_a_1667_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1654_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1654_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
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
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_b_1638_);
return v___x_1675_;
}
v___jp_1644_:
{
size_t v___x_1646_; size_t v___x_1647_; 
v___x_1646_ = ((size_t)1ULL);
v___x_1647_ = lean_usize_add(v_i_1636_, v___x_1646_);
v_i_1636_ = v___x_1647_;
v_b_1638_ = v_a_1645_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1635_ = stack[0].m_obj;
size_t v_i_1636_ = stack[1].m_num;
size_t v_stop_1637_ = stack[2].m_num;
lean_object* v_b_1638_ = stack[3].m_obj;
lean_object* v___y_1639_ = stack[4].m_obj;
lean_object* v___y_1640_ = stack[5].m_obj;
lean_object* v___y_1641_ = stack[6].m_obj;
lean_object* v___y_1642_ = stack[7].m_obj;
lean_object* v_res_1676_;
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_as_1635_, v_i_1636_, v_stop_1637_, v_b_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
stack->m_obj
 = v_res_1676_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___boxed(lean_object* v_as_1677_, lean_object* v_i_1678_, lean_object* v_stop_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
size_t v_i_boxed_1686_; size_t v_stop_boxed_1687_; lean_object* v_res_1688_; 
v_i_boxed_1686_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_stop_boxed_1687_ = lean_unbox_usize(v_stop_1679_);
lean_dec(v_stop_1679_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_as_1677_, v_i_boxed_1686_, v_stop_boxed_1687_, v_b_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v_as_1677_);
return v_res_1688_;
}
}
lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object* v___x_1689_, lean_object* v_decls_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1696_ = lean_mk_empty_array_with_capacity(v___x_1689_);
v___x_1697_ = lean_array_get_size(v_decls_1690_);
v___x_1698_ = lean_nat_dec_lt(v___x_1689_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1696_);
return v___x_1699_;
}
else
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_le(v___x_1697_, v___x_1697_);
if (v___x_1700_ == 0)
{
if (v___x_1698_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1696_);
return v___x_1701_;
}
else
{
size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = lean_usize_of_nat(v___x_1697_);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_1690_, v___x_1702_, v___x_1703_, v___x_1696_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1704_;
}
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1697_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_1690_, v___x_1705_, v___x_1706_, v___x_1696_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1707_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1689_ = stack[0].m_obj;
lean_object* v_decls_1690_ = stack[1].m_obj;
lean_object* v___y_1691_ = stack[2].m_obj;
lean_object* v___y_1692_ = stack[3].m_obj;
lean_object* v___y_1693_ = stack[4].m_obj;
lean_object* v___y_1694_ = stack[5].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(v___x_1689_, v_decls_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object* v___x_1709_, lean_object* v_decls_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(v___x_1709_, v_decls_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v_decls_1710_);
lean_dec(v___x_1709_);
return v_res_1716_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_unsigned_to_nat(4205464346u);
v___x_1785_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1786_ = l_Lean_Name_num___override(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1789_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1790_ = l_Lean_Name_str___override(v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1793_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1794_ = l_Lean_Name_str___override(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_unsigned_to_nat(2u);
v___x_1796_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1797_ = l_Lean_Name_num___override(v___x_1796_, v___x_1795_);
return v___x_1797_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1803_ = 1;
v___x_1804_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1805_ = l_Lean_registerTraceClass(v___x_1802_, v___x_1803_, v___x_1804_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec_ref_known(v___x_1805_, 1);
v___x_1806_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1807_ = l_Lean_registerTraceClass(v___x_1806_, v___x_1803_, v___x_1804_);
return v___x_1807_;
}
else
{
return v___x_1805_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1808_;
v_res_1808_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
return v_res_1810_;
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
