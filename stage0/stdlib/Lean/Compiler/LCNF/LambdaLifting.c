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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v_type_8_; lean_object* v___x_9_; 
v___x_7_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_type_8_ = lean_ctor_get(v___x_7_, 2);
lean_inc_ref(v_type_8_);
v___x_9_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_8_, v___y_4_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_26_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_26_ == 0)
{
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_26_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_26_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
uint8_t v___x_14_; 
v___x_14_ = 1;
if (lean_obj_tag(v_a_10_) == 0)
{
if (v___x_6_ == 0)
{
size_t v___x_15_; size_t v___x_16_; 
lean_del_object(v___x_12_);
v___x_15_ = ((size_t)1ULL);
v___x_16_ = lean_usize_add(v_i_2_, v___x_15_);
v_i_2_ = v___x_16_;
goto _start;
}
else
{
lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_18_ = lean_box(v___x_14_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_18_);
v___x_20_ = v___x_12_;
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
else
{
lean_object* v___x_22_; lean_object* v___x_24_; 
lean_dec_ref(v_a_10_);
v___x_22_ = lean_box(v___x_14_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_22_);
v___x_24_ = v___x_12_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
v_a_27_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_9_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_9_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = 0;
v___x_36_ = lean_box(v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object* v_as_38_, lean_object* v_i_39_, lean_object* v_stop_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
size_t v_i_boxed_43_; size_t v_stop_boxed_44_; lean_object* v_res_45_; 
v_i_boxed_43_ = lean_unbox_usize(v_i_39_);
lean_dec(v_i_39_);
v_stop_boxed_44_ = lean_unbox_usize(v_stop_40_);
lean_dec(v_stop_40_);
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_38_, v_i_boxed_43_, v_stop_boxed_44_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v_as_38_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object* v_decl_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_params_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_params_52_ = lean_ctor_get(v_decl_46_, 2);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_array_get_size(v_params_52_);
v___x_55_ = lean_nat_dec_lt(v___x_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
else
{
if (v___x_55_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_box(v___x_55_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
else
{
size_t v___x_60_; size_t v___x_61_; lean_object* v___x_62_; 
v___x_60_ = ((size_t)0ULL);
v___x_61_ = lean_usize_of_nat(v___x_54_);
v___x_62_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_params_52_, v___x_60_, v___x_61_, v_a_50_);
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object* v_decl_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec_ref(v_decl_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object* v_as_70_, size_t v_i_71_, size_t v_stop_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_70_, v_i_71_, v_stop_72_, v___y_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(v_as_79_, v_i_boxed_87_, v_stop_boxed_88_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec_ref(v_as_79_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object* v_decl_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_value_97_; uint8_t v_liftInstParamOnly_98_; lean_object* v_minSize_99_; uint8_t v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_value_97_ = lean_ctor_get(v_decl_90_, 4);
v_liftInstParamOnly_98_ = lean_ctor_get_uint8(v_a_91_, sizeof(void*)*3);
v_minSize_99_ = lean_ctor_get(v_a_91_, 2);
v___x_100_ = 0;
v___x_101_ = l_Lean_Compiler_LCNF_Code_size(v___x_100_, v_value_97_);
v___x_102_ = lean_nat_dec_lt(v___x_101_, v_minSize_99_);
lean_dec(v___x_101_);
if (v___x_102_ == 0)
{
if (v_liftInstParamOnly_98_ == 0)
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = 1;
v___x_104_ = lean_box(v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(v_decl_90_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
return v___x_106_;
}
}
else
{
uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = 0;
v___x_108_ = lean_box(v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object* v_decl_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_decl_118_, v_a_119_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object* v_decl_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(v_decl_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_decl_128_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; lean_object* v_decls_145_; lean_object* v_nextIdx_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_191_; 
v___x_144_ = lean_st_ref_take(v_a_139_);
v_decls_145_ = lean_ctor_get(v___x_144_, 0);
v_nextIdx_146_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_191_ == 0)
{
v___x_148_ = v___x_144_;
v_isShared_149_ = v_isSharedCheck_191_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_nextIdx_146_);
lean_inc(v_decls_145_);
lean_dec(v___x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_191_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_nextIdx_146_, v___x_150_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_151_);
v___x_153_ = v___x_148_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_decls_145_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_190_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_st_ref_set(v_a_139_, v___x_153_);
v___x_155_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_140_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_mainDecl_156_; lean_object* v_toSignature_157_; lean_object* v_a_158_; lean_object* v_suffix_159_; lean_object* v_name_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; 
v_mainDecl_156_ = lean_ctor_get(v_a_138_, 1);
v_toSignature_157_ = lean_ctor_get(v_mainDecl_156_, 0);
v_a_158_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v___x_155_);
v_suffix_159_ = lean_ctor_get(v_a_138_, 0);
v_name_160_ = lean_ctor_get(v_toSignature_157_, 0);
lean_inc(v_suffix_159_);
v___x_161_ = lean_name_append_index_after(v_suffix_159_, v_nextIdx_146_);
lean_inc(v_name_160_);
v___x_162_ = l_Lean_Name_append(v_name_160_, v___x_161_);
v___x_163_ = lean_unbox(v_a_158_);
lean_dec(v_a_158_);
lean_inc(v___x_162_);
v___x_164_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v___x_162_, v___x_163_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
if (lean_obj_tag(v_a_165_) == 1)
{
lean_dec_ref(v_a_165_);
lean_del_object(v___x_167_);
lean_dec(v___x_162_);
goto _start;
}
else
{
lean_object* v___x_171_; 
lean_dec(v_a_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_162_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_162_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v___x_162_);
v_a_174_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_164_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_nextIdx_146_);
v_a_182_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_155_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_155_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_199_, v_a_200_, v_a_202_, v_a_204_, v_a_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(lean_object* v_decl_217_, lean_object* v_value_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_fvarId_221_; lean_object* v_binderName_222_; lean_object* v_type_223_; lean_object* v___x_224_; lean_object* v_lctx_225_; lean_object* v_nextIdx_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_255_; 
v_fvarId_221_ = lean_ctor_get(v_decl_217_, 0);
v_binderName_222_ = lean_ctor_get(v_decl_217_, 1);
v_type_223_ = lean_ctor_get(v_decl_217_, 3);
v___x_224_ = lean_st_ref_take(v_a_219_);
v_lctx_225_ = lean_ctor_get(v___x_224_, 0);
v_nextIdx_226_ = lean_ctor_get(v___x_224_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_255_ == 0)
{
v___x_228_ = v___x_224_;
v_isShared_229_ = v_isSharedCheck_255_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_nextIdx_226_);
lean_inc(v_lctx_225_);
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_255_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
uint8_t v___x_230_; lean_object* v_declNew_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_230_ = 0;
lean_inc_ref(v_type_223_);
lean_inc(v_binderName_222_);
lean_inc(v_fvarId_221_);
v_declNew_231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_declNew_231_, 0, v_fvarId_221_);
lean_ctor_set(v_declNew_231_, 1, v_binderName_222_);
lean_ctor_set(v_declNew_231_, 2, v_type_223_);
lean_ctor_set(v_declNew_231_, 3, v_value_218_);
lean_inc_ref(v_declNew_231_);
v___x_232_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_230_, v_lctx_225_, v_declNew_231_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_232_);
v___x_234_ = v___x_228_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_nextIdx_226_);
v___x_234_ = v_reuseFailAlloc_254_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_st_ref_set(v_a_219_, v___x_234_);
v___x_236_ = 1;
v___x_237_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_230_, v_decl_217_, v___x_236_, v_a_219_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_245_);
v___x_239_ = v___x_237_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_dec(v___x_237_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v_declNew_231_);
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_declNew_231_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_declNew_231_);
v_a_246_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_237_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_237_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(lean_object* v_decl_256_, lean_object* v_value_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_256_, v_value_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_decl_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(lean_object* v_decl_261_, lean_object* v_value_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_261_, v_value_262_, v_a_267_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(lean_object* v_decl_272_, lean_object* v_value_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(v_decl_272_, v_value_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec_ref(v_decl_272_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t v_sz_283_, size_t v_i_284_, lean_object* v_bs_285_, uint8_t v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = lean_usize_dec_lt(v_i_284_, v_sz_283_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v_bs_285_);
return v___x_294_;
}
else
{
uint8_t v___x_295_; lean_object* v_v_296_; lean_object* v___x_297_; 
v___x_295_ = 0;
v_v_296_ = lean_array_uget_borrowed(v_bs_285_, v_i_284_);
lean_inc(v_v_296_);
v___x_297_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_295_, v_v_296_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; lean_object* v_bs_x27_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_unsigned_to_nat(0u);
v_bs_x27_300_ = lean_array_uset(v_bs_285_, v_i_284_, v___x_299_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_add(v_i_284_, v___x_301_);
v___x_303_ = lean_array_uset(v_bs_x27_300_, v_i_284_, v_a_298_);
v_i_284_ = v___x_302_;
v_bs_285_ = v___x_303_;
goto _start;
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v_bs_285_);
v_a_305_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_297_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_297_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object* v_sz_313_, lean_object* v_i_314_, lean_object* v_bs_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
size_t v_sz_boxed_323_; size_t v_i_boxed_324_; uint8_t v___y_2272__boxed_325_; lean_object* v_res_326_; 
v_sz_boxed_323_ = lean_unbox_usize(v_sz_313_);
lean_dec(v_sz_313_);
v_i_boxed_324_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v___y_2272__boxed_325_ = lean_unbox(v___y_316_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_boxed_323_, v_i_boxed_324_, v_bs_315_, v___y_2272__boxed_325_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object* v_closure_327_, lean_object* v_decl_328_, lean_object* v_nameNew_329_, uint8_t v_safe_330_, lean_object* v_inlineAttr_x3f_331_, uint8_t v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
size_t v_sz_339_; size_t v___x_340_; lean_object* v___x_341_; 
v_sz_339_ = lean_array_size(v_closure_327_);
v___x_340_ = ((size_t)0ULL);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_339_, v___x_340_, v_closure_327_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v_params_343_; lean_object* v_value_344_; size_t v_sz_345_; lean_object* v___x_346_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_341_);
v_params_343_ = lean_ctor_get(v_decl_328_, 2);
lean_inc_ref(v_params_343_);
v_value_344_ = lean_ctor_get(v_decl_328_, 4);
lean_inc_ref(v_value_344_);
lean_dec_ref(v_decl_328_);
v_sz_345_ = lean_array_size(v_params_343_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_345_, v___x_340_, v_params_343_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; uint8_t v___x_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v___x_348_ = 0;
v___x_349_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_348_, v_value_344_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc_n(v_a_350_, 2);
lean_dec_ref(v___x_349_);
v___x_351_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_348_, v_a_350_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = l_Array_append___redArg(v_a_342_, v_a_347_);
lean_dec(v_a_347_);
lean_inc_ref(v___x_353_);
v___x_354_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_348_, v___x_353_, v_a_352_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_368_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_368_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_368_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_368_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_a_350_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_361_, 0, v_nameNew_329_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_ctor_set(v___x_361_, 2, v_a_355_);
lean_ctor_set(v___x_361_, 3, v___x_353_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*4, v_safe_330_);
v___x_362_ = 0;
v___x_363_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_359_);
lean_ctor_set(v___x_363_, 2, v_inlineAttr_x3f_331_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*3, v___x_362_);
v___x_364_ = l_Lean_Compiler_LCNF_Decl_setLevelParams(v___x_363_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_364_);
v___x_366_ = v___x_357_;
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
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v___x_353_);
lean_dec(v_a_350_);
lean_dec(v_inlineAttr_x3f_331_);
lean_dec(v_nameNew_329_);
v_a_369_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_354_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_354_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_a_350_);
lean_dec(v_a_347_);
lean_dec(v_a_342_);
lean_dec(v_inlineAttr_x3f_331_);
lean_dec(v_nameNew_329_);
v_a_377_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_351_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_351_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_347_);
lean_dec(v_a_342_);
lean_dec(v_inlineAttr_x3f_331_);
lean_dec(v_nameNew_329_);
v_a_385_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_349_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_349_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_value_344_);
lean_dec(v_a_342_);
lean_dec(v_inlineAttr_x3f_331_);
lean_dec(v_nameNew_329_);
v_a_393_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_346_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_346_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_inlineAttr_x3f_331_);
lean_dec(v_nameNew_329_);
lean_dec_ref(v_decl_328_);
v_a_401_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_341_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_341_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object* v_closure_409_, lean_object* v_decl_410_, lean_object* v_nameNew_411_, lean_object* v_safe_412_, lean_object* v_inlineAttr_x3f_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
uint8_t v_safe_boxed_421_; uint8_t v_a_boxed_422_; lean_object* v_res_423_; 
v_safe_boxed_421_ = lean_unbox(v_safe_412_);
v_a_boxed_422_ = lean_unbox(v_a_414_);
v_res_423_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_409_, v_decl_410_, v_nameNew_411_, v_safe_boxed_421_, v_inlineAttr_x3f_413_, v_a_boxed_422_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
if (lean_obj_tag(v_a_424_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = l_List_reverse___redArg(v_a_425_);
return v___x_426_;
}
else
{
lean_object* v_head_427_; lean_object* v_tail_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v_head_427_ = lean_ctor_get(v_a_424_, 0);
v_tail_428_ = lean_ctor_get(v_a_424_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_437_ == 0)
{
v___x_430_ = v_a_424_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_tail_428_);
lean_inc(v_head_427_);
lean_dec(v_a_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_mkLevelParam(v_head_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_a_425_);
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_a_425_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_a_424_ = v_tail_428_;
v_a_425_ = v___x_434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t v_sz_438_, size_t v_i_439_, lean_object* v_bs_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = lean_usize_dec_lt(v_i_439_, v_sz_438_);
if (v___x_441_ == 0)
{
return v_bs_440_;
}
else
{
lean_object* v_v_442_; lean_object* v_fvarId_443_; lean_object* v___x_444_; lean_object* v_bs_x27_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_v_442_ = lean_array_uget_borrowed(v_bs_440_, v_i_439_);
v_fvarId_443_ = lean_ctor_get(v_v_442_, 0);
lean_inc(v_fvarId_443_);
v___x_444_ = lean_unsigned_to_nat(0u);
v_bs_x27_445_ = lean_array_uset(v_bs_440_, v_i_439_, v___x_444_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_fvarId_443_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_439_, v___x_447_);
v___x_449_ = lean_array_uset(v_bs_x27_445_, v_i_439_, v___x_446_);
v_i_439_ = v___x_448_;
v_bs_440_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_bs_453_){
_start:
{
size_t v_sz_boxed_454_; size_t v_i_boxed_455_; lean_object* v_res_456_; 
v_sz_boxed_454_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_boxed_454_, v_i_boxed_455_, v_bs_453_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_box(0);
v___x_458_ = lean_unsigned_to_nat(16u);
v___x_459_ = lean_mk_array(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object* v_closure_463_, lean_object* v_decl_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___y_473_; lean_object* v_auxDeclName_474_; lean_object* v___y_475_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v_a_489_; lean_object* v___x_536_; 
v___x_536_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(v_a_465_, v_a_466_, v_a_467_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_inlineAttr_x3f_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; uint8_t v_inheritInlineAttrs_566_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref(v___x_536_);
v_inheritInlineAttrs_566_ = lean_ctor_get_uint8(v_a_465_, sizeof(void*)*3 + 1);
if (v_inheritInlineAttrs_566_ == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_box(0);
v_inlineAttr_x3f_539_ = v___x_567_;
v___y_540_ = v_a_465_;
v___y_541_ = v_a_466_;
v___y_542_ = v_a_467_;
v___y_543_ = v_a_468_;
v___y_544_ = v_a_469_;
v___y_545_ = v_a_470_;
goto v___jp_538_;
}
else
{
lean_object* v_mainDecl_568_; lean_object* v_inlineAttr_x3f_569_; 
v_mainDecl_568_ = lean_ctor_get(v_a_465_, 1);
v_inlineAttr_x3f_569_ = lean_ctor_get(v_mainDecl_568_, 2);
v_inlineAttr_x3f_539_ = v_inlineAttr_x3f_569_;
v___y_540_ = v_a_465_;
v___y_541_ = v_a_466_;
v___y_542_ = v_a_467_;
v___y_543_ = v_a_468_;
v___y_544_ = v_a_469_;
v___y_545_ = v_a_470_;
goto v___jp_538_;
}
v___jp_538_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_mainDecl_549_; lean_object* v_toSignature_550_; uint8_t v_safe_551_; uint8_t v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1);
v___x_548_ = lean_st_mk_ref(v___x_547_);
v_mainDecl_549_ = lean_ctor_get(v___y_540_, 1);
v_toSignature_550_ = lean_ctor_get(v_mainDecl_549_, 0);
v_safe_551_ = lean_ctor_get_uint8(v_toSignature_550_, sizeof(void*)*4);
v___x_552_ = 0;
v___x_553_ = 0;
lean_inc(v_inlineAttr_x3f_539_);
lean_inc_ref(v_decl_464_);
lean_inc_ref(v_closure_463_);
v___x_554_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_463_, v_decl_464_, v_a_537_, v_safe_551_, v_inlineAttr_x3f_539_, v___x_553_, v___x_548_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref(v___x_554_);
v___x_556_ = lean_st_ref_get(v___x_548_);
lean_dec(v___x_548_);
lean_dec(v___x_556_);
v___y_482_ = v___y_542_;
v___y_483_ = v___y_543_;
v___y_484_ = v___y_545_;
v___y_485_ = v___y_541_;
v___y_486_ = v___y_544_;
v___y_487_ = v___x_546_;
v___y_488_ = v___x_552_;
v_a_489_ = v_a_555_;
goto v___jp_481_;
}
else
{
lean_dec(v___x_548_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_557_; 
v_a_557_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_557_);
lean_dec_ref(v___x_554_);
v___y_482_ = v___y_542_;
v___y_483_ = v___y_543_;
v___y_484_ = v___y_545_;
v___y_485_ = v___y_541_;
v___y_486_ = v___y_544_;
v___y_487_ = v___x_546_;
v___y_488_ = v___x_552_;
v_a_489_ = v_a_557_;
goto v___jp_481_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec_ref(v_decl_464_);
lean_dec_ref(v_closure_463_);
v_a_558_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_554_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_decl_464_);
lean_dec_ref(v_closure_463_);
v_a_570_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_536_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_536_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
v___jp_472_:
{
size_t v_sz_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_sz_476_ = lean_array_size(v_closure_463_);
v___x_477_ = ((size_t)0ULL);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_476_, v___x_477_, v_closure_463_);
v___x_479_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_479_, 0, v_auxDeclName_474_);
lean_ctor_set(v___x_479_, 1, v___y_473_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
v___x_480_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_464_, v___x_479_, v___y_475_);
lean_dec_ref(v_decl_464_);
return v___x_480_;
}
v___jp_481_:
{
lean_object* v_toSignature_490_; lean_object* v___x_491_; 
v_toSignature_490_ = lean_ctor_get(v_a_489_, 0);
lean_inc_ref(v_a_489_);
v___x_491_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___y_488_, v_a_489_, v___y_486_, v___y_484_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v_name_493_; lean_object* v_levelParams_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_491_);
v_name_493_ = lean_ctor_get(v_toSignature_490_, 0);
v_levelParams_494_ = lean_ctor_get(v_toSignature_490_, 1);
v___x_495_ = lean_box(0);
lean_inc(v_levelParams_494_);
v___x_496_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(v_levelParams_494_, v___x_495_);
if (lean_obj_tag(v_a_492_) == 0)
{
lean_object* v___x_497_; 
lean_inc(v_name_493_);
lean_inc_ref(v_a_489_);
v___x_497_ = l_Lean_Compiler_LCNF_Decl_save(v___y_488_, v_a_489_, v___y_482_, v___y_483_, v___y_486_, v___y_484_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; lean_object* v_decls_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v___x_497_);
v___x_498_ = lean_st_ref_take(v___y_485_);
v_decls_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_498_, 1);
lean_dec(v_unused_509_);
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_decls_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_array_push(v_decls_499_, v_a_489_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___y_487_);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___y_487_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_st_ref_set(v___y_485_, v___x_505_);
v___y_473_ = v___x_496_;
v_auxDeclName_474_ = v_name_493_;
v___y_475_ = v___y_483_;
goto v___jp_472_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v___x_496_);
lean_dec(v_name_493_);
lean_dec_ref(v_a_489_);
lean_dec(v___y_487_);
lean_dec_ref(v_decl_464_);
lean_dec_ref(v_closure_463_);
v_a_510_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_497_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_497_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_declName_518_; lean_object* v___x_519_; 
lean_dec(v___y_487_);
v_declName_518_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_declName_518_);
lean_dec_ref(v_a_492_);
v___x_519_ = l_Lean_Compiler_LCNF_eraseDecl(v___y_488_, v_a_489_, v___y_482_, v___y_483_, v___y_486_, v___y_484_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_dec_ref(v___x_519_);
v___y_473_ = v___x_496_;
v_auxDeclName_474_ = v_declName_518_;
v___y_475_ = v___y_483_;
goto v___jp_472_;
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_declName_518_);
lean_dec(v___x_496_);
lean_dec_ref(v_decl_464_);
lean_dec_ref(v_closure_463_);
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_a_489_);
lean_dec(v___y_487_);
lean_dec_ref(v_decl_464_);
lean_dec_ref(v_closure_463_);
v_a_528_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_491_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_491_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object* v_closure_578_, lean_object* v_decl_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_578_, v_decl_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object* v_closure_588_, lean_object* v_decl_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_closure_588_, v_decl_589_, v_a_590_, v_a_591_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object* v_closure_599_, lean_object* v_decl_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(v_closure_599_, v_decl_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(lean_object* v_as_612_, size_t v_sz_613_, size_t v_i_614_, lean_object* v_b_615_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_615_);
return v___x_618_;
}
else
{
lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_671_; 
v_snd_619_ = lean_ctor_get(v_b_615_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_b_615_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_b_615_, 0);
lean_dec(v_unused_672_);
v___x_621_ = v_b_615_;
v_isShared_622_ = v_isSharedCheck_671_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_dec(v_b_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_671_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_array_623_; lean_object* v_start_624_; lean_object* v_stop_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_array_623_ = lean_ctor_get(v_snd_619_, 0);
v_start_624_ = lean_ctor_get(v_snd_619_, 1);
v_stop_625_ = lean_ctor_get(v_snd_619_, 2);
v___x_626_ = lean_box(0);
v___x_627_ = lean_nat_dec_lt(v_start_624_, v_stop_625_);
if (v___x_627_ == 0)
{
lean_object* v___x_629_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_626_);
v___x_629_ = v___x_621_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_snd_619_);
v___x_629_ = v_reuseFailAlloc_631_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
else
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_667_; 
lean_inc(v_stop_625_);
lean_inc(v_start_624_);
lean_inc_ref(v_array_623_);
v_isSharedCheck_667_ = !lean_is_exclusive(v_snd_619_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_668_ = lean_ctor_get(v_snd_619_, 2);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_snd_619_, 1);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_snd_619_, 0);
lean_dec(v_unused_670_);
v___x_633_ = v_snd_619_;
v_isShared_634_ = v_isSharedCheck_667_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_snd_619_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_667_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_a_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v_a_635_ = lean_array_uget(v_as_612_, v_i_614_);
v___x_636_ = lean_array_fget(v_array_623_, v_start_624_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_start_624_, v___x_637_);
lean_dec(v_start_624_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_638_);
v___x_640_ = v___x_633_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_array_623_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_stop_625_);
v___x_640_ = v_reuseFailAlloc_666_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
if (lean_obj_tag(v_a_635_) == 1)
{
lean_object* v_fvarId_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_660_; 
v_fvarId_641_ = lean_ctor_get(v_a_635_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_635_);
if (v_isSharedCheck_660_ == 0)
{
v___x_643_ = v_a_635_;
v_isShared_644_ = v_isSharedCheck_660_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_fvarId_641_);
lean_dec(v_a_635_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_660_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_fvarId_645_; uint8_t v___x_646_; 
v_fvarId_645_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_fvarId_645_);
lean_dec(v___x_636_);
v___x_646_ = l_Lean_instBEqFVarId_beq(v_fvarId_641_, v_fvarId_645_);
lean_dec(v_fvarId_645_);
lean_dec(v_fvarId_641_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_640_);
lean_ctor_set(v___x_621_, 0, v___x_647_);
v___x_649_ = v___x_621_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_640_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 0);
lean_ctor_set(v___x_643_, 0, v___x_649_);
v___x_651_ = v___x_643_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_del_object(v___x_643_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_640_);
lean_ctor_set(v___x_621_, 0, v___x_626_);
v___x_655_ = v___x_621_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_640_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
size_t v___x_656_; size_t v___x_657_; 
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_add(v_i_614_, v___x_656_);
v_i_614_ = v___x_657_;
v_b_615_ = v___x_655_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec(v___x_636_);
lean_dec(v_a_635_);
v___x_661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_640_);
lean_ctor_set(v___x_621_, 0, v___x_661_);
v___x_663_ = v___x_621_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_640_);
v___x_663_ = v_reuseFailAlloc_665_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(lean_object* v_as_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_b_676_, lean_object* v___y_677_){
_start:
{
size_t v_sz_boxed_678_; size_t v_i_boxed_679_; lean_object* v_res_680_; 
v_sz_boxed_678_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_679_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_673_, v_sz_boxed_678_, v_i_boxed_679_, v_b_676_);
lean_dec_ref(v_as_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(lean_object* v_decl_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
uint8_t v_allowEtaContraction_695_; 
v_allowEtaContraction_695_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*3 + 2);
if (v_allowEtaContraction_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref(v_decl_683_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
else
{
lean_object* v_value_698_; 
v_value_698_ = lean_ctor_get(v_decl_683_, 4);
lean_inc_ref(v_value_698_);
if (lean_obj_tag(v_value_698_) == 0)
{
lean_object* v_decl_699_; lean_object* v_value_700_; 
v_decl_699_ = lean_ctor_get(v_value_698_, 0);
lean_inc_ref(v_decl_699_);
v_value_700_ = lean_ctor_get(v_decl_699_, 3);
lean_inc(v_value_700_);
if (lean_obj_tag(v_value_700_) == 3)
{
lean_object* v_k_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_816_; 
v_k_701_ = lean_ctor_get(v_value_698_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_value_698_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_value_698_, 0);
lean_dec(v_unused_817_);
v___x_703_ = v_value_698_;
v_isShared_704_ = v_isSharedCheck_816_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_k_701_);
lean_dec(v_value_698_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_816_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
if (lean_obj_tag(v_k_701_) == 5)
{
lean_object* v_params_705_; lean_object* v_fvarId_706_; lean_object* v_declName_707_; lean_object* v_us_708_; lean_object* v_args_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_815_; 
v_params_705_ = lean_ctor_get(v_decl_683_, 2);
v_fvarId_706_ = lean_ctor_get(v_decl_699_, 0);
lean_inc(v_fvarId_706_);
lean_dec_ref(v_decl_699_);
v_declName_707_ = lean_ctor_get(v_value_700_, 0);
v_us_708_ = lean_ctor_get(v_value_700_, 1);
v_args_709_ = lean_ctor_get(v_value_700_, 2);
v_isSharedCheck_815_ = !lean_is_exclusive(v_value_700_);
if (v_isSharedCheck_815_ == 0)
{
v___x_711_ = v_value_700_;
v_isShared_712_ = v_isSharedCheck_815_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_args_709_);
lean_inc(v_us_708_);
lean_inc(v_declName_707_);
lean_dec(v_value_700_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_815_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_fvarId_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_814_; 
v_fvarId_713_ = lean_ctor_get(v_k_701_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_k_701_);
if (v_isSharedCheck_814_ == 0)
{
v___x_715_ = v_k_701_;
v_isShared_716_ = v_isSharedCheck_814_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_fvarId_713_);
lean_dec(v_k_701_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_814_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_instBEqFVarId_beq(v_fvarId_706_, v_fvarId_713_);
lean_dec(v_fvarId_713_);
lean_dec(v_fvarId_706_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_del_object(v___x_711_);
lean_dec_ref(v_args_709_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_del_object(v___x_703_);
lean_dec_ref(v_decl_683_);
v___x_718_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 0, v___x_718_);
v___x_720_ = v___x_715_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_array_get_size(v_args_709_);
v___x_723_ = lean_array_get_size(v_params_705_);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_727_; 
lean_del_object(v___x_711_);
lean_dec_ref(v_args_709_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_del_object(v___x_703_);
lean_dec_ref(v_decl_683_);
v___x_725_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 0, v___x_725_);
v___x_727_ = v___x_715_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_729_; 
lean_del_object(v___x_715_);
v___x_729_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_687_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; uint8_t v___x_731_; lean_object* v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = lean_unbox(v_a_730_);
lean_dec(v_a_730_);
lean_inc(v_declName_707_);
v___x_732_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_707_, v___x_731_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_797_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_797_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_797_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_797_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 1)
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_735_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_733_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_a_733_, 0);
lean_dec(v_unused_792_);
v___x_738_ = v_a_733_;
v_isShared_739_ = v_isSharedCheck_791_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_a_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_791_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_740_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_params_705_);
v___x_741_ = l_Array_toSubarray___redArg(v_params_705_, v___x_740_, v___x_723_);
v___x_742_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_741_);
lean_ctor_set(v___x_703_, 0, v___x_742_);
v___x_744_ = v___x_703_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_741_);
v___x_744_ = v_reuseFailAlloc_790_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
size_t v_sz_745_; size_t v___x_746_; lean_object* v___x_747_; 
v_sz_745_ = lean_array_size(v_args_709_);
v___x_746_ = ((size_t)0ULL);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_args_709_, v_sz_745_, v___x_746_, v___x_744_);
lean_dec_ref(v_args_709_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_781_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_781_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_781_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_781_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_fst_752_; 
v_fst_752_ = lean_ctor_get(v_a_748_, 0);
lean_inc(v_fst_752_);
lean_dec(v_a_748_);
if (lean_obj_tag(v_fst_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_del_object(v___x_750_);
v___x_753_ = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0));
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v___x_753_);
v___x_755_ = v___x_711_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_declName_707_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_us_708_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_753_);
v___x_755_ = v_reuseFailAlloc_776_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(v_decl_683_, v___x_755_, v_a_688_);
lean_dec_ref(v_decl_683_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_767_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_767_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_a_757_);
v___x_762_ = v___x_738_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_762_);
v___x_764_ = v___x_759_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_738_);
v_a_768_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_756_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_756_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
else
{
lean_object* v_val_777_; lean_object* v___x_779_; 
lean_del_object(v___x_738_);
lean_del_object(v___x_711_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_dec_ref(v_decl_683_);
v_val_777_ = lean_ctor_get(v_fst_752_, 0);
lean_inc(v_val_777_);
lean_dec_ref(v_fst_752_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v_val_777_);
v___x_779_ = v___x_750_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_val_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_del_object(v___x_738_);
lean_del_object(v___x_711_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_dec_ref(v_decl_683_);
v_a_782_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_747_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_747_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec(v_a_733_);
lean_del_object(v___x_711_);
lean_dec_ref(v_args_709_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_del_object(v___x_703_);
lean_dec_ref(v_decl_683_);
v___x_793_ = lean_box(0);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_793_);
v___x_795_ = v___x_735_;
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
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_del_object(v___x_711_);
lean_dec_ref(v_args_709_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_del_object(v___x_703_);
lean_dec_ref(v_decl_683_);
v_a_798_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_732_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_732_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_del_object(v___x_711_);
lean_dec_ref(v_args_709_);
lean_dec(v_us_708_);
lean_dec(v_declName_707_);
lean_del_object(v___x_703_);
lean_dec_ref(v_decl_683_);
v_a_806_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_729_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_729_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
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
lean_del_object(v___x_703_);
lean_dec_ref(v_value_700_);
lean_dec_ref(v_k_701_);
lean_dec_ref(v_decl_699_);
lean_dec_ref(v_decl_683_);
goto v___jp_692_;
}
}
}
else
{
lean_dec(v_value_700_);
lean_dec_ref(v_value_698_);
lean_dec_ref(v_decl_699_);
lean_dec_ref(v_decl_683_);
goto v___jp_692_;
}
}
else
{
lean_dec_ref(v_value_698_);
lean_dec_ref(v_decl_683_);
goto v___jp_692_;
}
}
v___jp_692_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(lean_object* v_decl_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_decl_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(lean_object* v_as_828_, size_t v_sz_829_, size_t v_i_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_828_, v_sz_829_, v_i_830_, v_b_831_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(lean_object* v_as_841_, lean_object* v_sz_842_, lean_object* v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
size_t v_sz_boxed_853_; size_t v_i_boxed_854_; lean_object* v_res_855_; 
v_sz_boxed_853_ = lean_unbox_usize(v_sz_842_);
lean_dec(v_sz_842_);
v_i_boxed_854_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(v_as_841_, v_sz_boxed_853_, v_i_boxed_854_, v_b_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v_as_841_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object* v_as_856_, size_t v_i_857_, size_t v_stop_858_, lean_object* v_b_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_eq(v_i_857_, v_stop_858_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v_fvarId_862_; lean_object* v___x_863_; size_t v___x_864_; size_t v___x_865_; 
v___x_861_ = lean_array_uget_borrowed(v_as_856_, v_i_857_);
v_fvarId_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_fvarId_862_);
v___x_863_ = l_Lean_FVarIdSet_insert(v_b_859_, v_fvarId_862_);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_857_, v___x_864_);
v_i_857_ = v___x_865_;
v_b_859_ = v___x_863_;
goto _start;
}
else
{
return v_b_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object* v_as_867_, lean_object* v_i_868_, lean_object* v_stop_869_, lean_object* v_b_870_){
_start:
{
size_t v_i_boxed_871_; size_t v_stop_boxed_872_; lean_object* v_res_873_; 
v_i_boxed_871_ = lean_unbox_usize(v_i_868_);
lean_dec(v_i_868_);
v_stop_boxed_872_ = lean_unbox_usize(v_stop_869_);
lean_dec(v_stop_869_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_as_867_, v_i_boxed_871_, v_stop_boxed_872_, v_b_870_);
lean_dec_ref(v_as_867_);
return v_res_873_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(lean_object* v_k_874_, lean_object* v_t_875_){
_start:
{
if (lean_obj_tag(v_t_875_) == 0)
{
lean_object* v_k_876_; lean_object* v_l_877_; lean_object* v_r_878_; uint8_t v___x_879_; 
v_k_876_ = lean_ctor_get(v_t_875_, 1);
v_l_877_ = lean_ctor_get(v_t_875_, 3);
v_r_878_ = lean_ctor_get(v_t_875_, 4);
v___x_879_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_874_, v_k_876_);
switch(v___x_879_)
{
case 0:
{
v_t_875_ = v_l_877_;
goto _start;
}
case 1:
{
uint8_t v___x_881_; 
v___x_881_ = 1;
return v___x_881_;
}
default: 
{
v_t_875_ = v_r_878_;
goto _start;
}
}
}
else
{
uint8_t v___x_883_; 
v___x_883_ = 0;
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(lean_object* v_k_884_, lean_object* v_t_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_884_, v_t_885_);
lean_dec(v_t_885_);
lean_dec(v_k_884_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object* v_a_888_, lean_object* v___y_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v___y_889_, v_a_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object* v_a_891_, lean_object* v___y_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(v_a_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec(v_a_891_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t v_a_895_, lean_object* v_x_896_){
_start:
{
return v_a_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object* v_a_897_, lean_object* v_x_898_){
_start:
{
uint8_t v_a_14208__boxed_899_; uint8_t v_res_900_; lean_object* v_r_901_; 
v_a_14208__boxed_899_ = lean_unbox(v_a_897_);
v_res_900_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(v_a_14208__boxed_899_, v_x_898_);
lean_dec(v_x_898_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(lean_object* v_i_902_, lean_object* v_as_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_array_get_size(v_as_903_);
v___x_913_ = lean_nat_dec_lt(v_i_902_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v_i_902_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_as_903_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v_a_917_; lean_object* v_a_929_; 
v_a_915_ = lean_array_fget_borrowed(v_as_903_, v_i_902_);
if (lean_obj_tag(v_a_915_) == 0)
{
lean_object* v_params_931_; lean_object* v_code_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_params_931_ = lean_ctor_get(v_a_915_, 1);
v_code_932_ = lean_ctor_get(v_a_915_, 2);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_array_get_size(v_params_931_);
v___x_935_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_inc_ref(v_code_932_);
v___x_936_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_932_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
lean_inc_ref(v_a_915_);
v___x_938_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_915_, v_a_937_);
v_a_917_ = v___x_938_;
goto v___jp_916_;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_as_903_);
lean_dec(v_i_902_);
v_a_939_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_936_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_936_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
uint8_t v___x_947_; 
v___x_947_ = lean_nat_dec_le(v___x_934_, v___x_934_);
if (v___x_947_ == 0)
{
if (v___x_935_ == 0)
{
lean_object* v___x_948_; 
lean_inc_ref(v_code_932_);
v___x_948_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_932_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___x_948_);
v_a_929_ = v_a_949_;
goto v___jp_928_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_as_903_);
lean_dec(v_i_902_);
v_a_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_934_);
lean_inc(v___y_906_);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_931_, v___x_958_, v___x_959_, v___y_906_);
lean_inc_ref(v_code_932_);
v___x_961_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_932_, v___y_904_, v___y_905_, v___x_960_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v_a_929_ = v_a_962_;
goto v___jp_928_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_as_903_);
lean_dec(v_i_902_);
v_a_963_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_961_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_961_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_971_ = ((size_t)0ULL);
v___x_972_ = lean_usize_of_nat(v___x_934_);
lean_inc(v___y_906_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_931_, v___x_971_, v___x_972_, v___y_906_);
lean_inc_ref(v_code_932_);
v___x_974_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_932_, v___y_904_, v___y_905_, v___x_973_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v___x_974_);
v_a_929_ = v_a_975_;
goto v___jp_928_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v_as_903_);
lean_dec(v_i_902_);
v_a_976_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_974_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
else
{
lean_object* v_code_984_; lean_object* v___x_985_; 
v_code_984_ = lean_ctor_get(v_a_915_, 0);
lean_inc_ref(v_code_984_);
v___x_985_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_984_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
lean_inc_ref(v_a_915_);
v___x_987_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_915_, v_a_986_);
v_a_917_ = v___x_987_;
goto v___jp_916_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_as_903_);
lean_dec(v_i_902_);
v_a_988_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_985_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_985_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
v___jp_916_:
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_ptr_addr(v_a_915_);
v___x_919_ = lean_ptr_addr(v_a_917_);
v___x_920_ = lean_usize_dec_eq(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_i_902_, v___x_921_);
v___x_923_ = lean_array_fset(v_as_903_, v_i_902_, v_a_917_);
lean_dec(v_i_902_);
v_i_902_ = v___x_922_;
v_as_903_ = v___x_923_;
goto _start;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_a_917_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_i_902_, v___x_925_);
lean_dec(v_i_902_);
v_i_902_ = v___x_926_;
goto _start;
}
}
v___jp_928_:
{
lean_object* v___x_930_; 
lean_inc(v_a_915_);
v___x_930_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_915_, v_a_929_);
v_a_917_ = v___x_930_;
goto v___jp_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object* v_code_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
switch(lean_obj_tag(v_code_996_))
{
case 0:
{
lean_object* v_decl_1005_; lean_object* v_k_1006_; lean_object* v_fvarId_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_decl_1005_ = lean_ctor_get(v_code_996_, 0);
v_k_1006_ = lean_ctor_get(v_code_996_, 1);
v_fvarId_1007_ = lean_ctor_get(v_decl_1005_, 0);
lean_inc(v_fvarId_1007_);
lean_inc(v_a_999_);
v___x_1008_ = l_Lean_FVarIdSet_insert(v_a_999_, v_fvarId_1007_);
lean_inc_ref(v_k_1006_);
v___x_1009_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1006_, v_a_997_, v_a_998_, v___x_1008_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v___x_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1036_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1036_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1036_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v___y_1015_; size_t v___x_1031_; size_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = lean_ptr_addr(v_k_1006_);
v___x_1032_ = lean_ptr_addr(v_a_1010_);
v___x_1033_ = lean_usize_dec_eq(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
v___y_1015_ = v___x_1033_;
goto v___jp_1014_;
}
else
{
size_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_ptr_addr(v_decl_1005_);
v___x_1035_ = lean_usize_dec_eq(v___x_1034_, v___x_1034_);
v___y_1015_ = v___x_1035_;
goto v___jp_1014_;
}
v___jp_1014_:
{
if (v___y_1015_ == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1025_; 
lean_inc_ref(v_decl_1005_);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_code_996_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1026_ = lean_ctor_get(v_code_996_, 1);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_code_996_, 0);
lean_dec(v_unused_1027_);
v___x_1017_ = v_code_996_;
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v_code_996_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v_a_1010_);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_decl_1005_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1010_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1020_);
v___x_1022_ = v___x_1012_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v___x_1029_; 
lean_dec(v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_code_996_);
v___x_1029_ = v___x_1012_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_code_996_);
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
}
else
{
lean_dec_ref(v_code_996_);
return v___x_1009_;
}
}
case 1:
{
lean_object* v_decl_1037_; lean_object* v_k_1038_; lean_object* v_declNew_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___x_1060_; 
v_decl_1037_ = lean_ctor_get(v_code_996_, 0);
v_k_1038_ = lean_ctor_get(v_code_996_, 1);
lean_inc_ref(v_decl_1037_);
v___x_1060_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_decl_1037_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(v_a_1061_, v_a_997_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; uint8_t v___x_1064_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = lean_unbox(v_a_1063_);
if (v___x_1064_ == 0)
{
lean_object* v_fvarId_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_a_1063_);
v_fvarId_1065_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_fvarId_1065_);
lean_inc(v_a_999_);
v___x_1066_ = l_Lean_FVarIdSet_insert(v_a_999_, v_fvarId_1065_);
lean_inc_ref(v_k_1038_);
v___x_1067_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1038_, v_a_997_, v_a_998_, v___x_1066_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1095_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1095_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1095_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___y_1073_; size_t v___x_1089_; size_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_ptr_addr(v_k_1038_);
v___x_1090_ = lean_ptr_addr(v_a_1068_);
v___x_1091_ = lean_usize_dec_eq(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
v___y_1073_ = v___x_1091_;
goto v___jp_1072_;
}
else
{
size_t v___x_1092_; size_t v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = lean_ptr_addr(v_decl_1037_);
v___x_1093_ = lean_ptr_addr(v_a_1061_);
v___x_1094_ = lean_usize_dec_eq(v___x_1092_, v___x_1093_);
v___y_1073_ = v___x_1094_;
goto v___jp_1072_;
}
v___jp_1072_:
{
if (v___y_1073_ == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1083_; 
v_isSharedCheck_1083_ = !lean_is_exclusive(v_code_996_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; lean_object* v_unused_1085_; 
v_unused_1084_ = lean_ctor_get(v_code_996_, 1);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_code_996_, 0);
lean_dec(v_unused_1085_);
v___x_1075_ = v_code_996_;
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v_code_996_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_a_1068_);
lean_ctor_set(v___x_1075_, 0, v_a_1061_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1061_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1068_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1078_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v___x_1087_; 
lean_dec(v_a_1068_);
lean_dec(v_a_1061_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v_code_996_);
v___x_1087_ = v___x_1070_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_code_996_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_dec(v_a_1061_);
lean_dec_ref(v_code_996_);
return v___x_1067_;
}
}
else
{
lean_object* v___x_1096_; 
lean_inc_ref(v_k_1038_);
lean_dec_ref(v_code_996_);
lean_inc(v_a_1061_);
v___x_1096_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(v_a_1061_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1096_);
if (lean_obj_tag(v_a_1097_) == 1)
{
lean_object* v_val_1098_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1061_);
v_val_1098_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_val_1098_);
lean_dec_ref(v_a_1097_);
v_declNew_1040_ = v_val_1098_;
v___y_1041_ = v_a_997_;
v___y_1042_ = v_a_998_;
v___y_1043_ = v_a_999_;
v___y_1044_ = v_a_1000_;
v___y_1045_ = v_a_1001_;
v___y_1046_ = v_a_1002_;
v___y_1047_ = v_a_1003_;
goto v___jp_1039_;
}
else
{
lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_a_1097_);
lean_inc(v_a_999_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1099_, 0, v_a_999_);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1100_, 0, v_a_1063_);
lean_inc(v_a_1061_);
v___x_1101_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed), 8, 1);
lean_closure_set(v___x_1101_, 0, v_a_1061_);
v___x_1102_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v___x_1101_, v___f_1099_, v___f_1100_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v_snd_1104_; lean_object* v_fst_1105_; lean_object* v___x_1106_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v_snd_1104_ = lean_ctor_get(v_a_1103_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_a_1103_);
v_fst_1105_ = lean_ctor_get(v_snd_1104_, 0);
lean_inc(v_fst_1105_);
lean_dec(v_snd_1104_);
v___x_1106_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_fst_1105_, v_a_1061_, v_a_997_, v_a_998_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
v_declNew_1040_ = v_a_1107_;
v___y_1041_ = v_a_997_;
v___y_1042_ = v_a_998_;
v___y_1043_ = v_a_999_;
v___y_1044_ = v_a_1000_;
v___y_1045_ = v_a_1001_;
v___y_1046_ = v_a_1002_;
v___y_1047_ = v_a_1003_;
goto v___jp_1039_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_k_1038_);
v_a_1108_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1106_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_a_1061_);
lean_dec_ref(v_k_1038_);
v_a_1116_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1102_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1102_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1061_);
lean_dec_ref(v_k_1038_);
v_a_1124_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1096_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1096_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_a_1061_);
lean_dec_ref(v_code_996_);
v_a_1132_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1062_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1062_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_code_996_);
v_a_1140_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1060_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1060_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
v___jp_1039_:
{
lean_object* v_fvarId_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_fvarId_1048_ = lean_ctor_get(v_declNew_1040_, 0);
lean_inc(v_fvarId_1048_);
lean_inc(v___y_1043_);
v___x_1049_ = l_Lean_FVarIdSet_insert(v___y_1043_, v_fvarId_1048_);
v___x_1050_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1038_, v___y_1041_, v___y_1042_, v___x_1049_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___x_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_declNew_1040_);
lean_ctor_set(v___x_1055_, 1, v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_dec_ref(v_declNew_1040_);
return v___x_1050_;
}
}
}
case 2:
{
lean_object* v_decl_1148_; lean_object* v_k_1149_; lean_object* v___x_1150_; 
v_decl_1148_ = lean_ctor_get(v_code_996_, 0);
v_k_1149_ = lean_ctor_get(v_code_996_, 1);
lean_inc_ref(v_decl_1148_);
v___x_1150_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_decl_1148_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v_fvarId_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v_fvarId_1152_ = lean_ctor_get(v_a_1151_, 0);
lean_inc(v_fvarId_1152_);
lean_inc(v_a_999_);
v___x_1153_ = l_Lean_FVarIdSet_insert(v_a_999_, v_fvarId_1152_);
lean_inc_ref(v_k_1149_);
v___x_1154_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_k_1149_, v_a_997_, v_a_998_, v___x_1153_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1182_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1182_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1182_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___y_1160_; size_t v___x_1176_; size_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_ptr_addr(v_k_1149_);
v___x_1177_ = lean_ptr_addr(v_a_1155_);
v___x_1178_ = lean_usize_dec_eq(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
v___y_1160_ = v___x_1178_;
goto v___jp_1159_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_ptr_addr(v_decl_1148_);
v___x_1180_ = lean_ptr_addr(v_a_1151_);
v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
v___y_1160_ = v___x_1181_;
goto v___jp_1159_;
}
v___jp_1159_:
{
if (v___y_1160_ == 0)
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1170_; 
v_isSharedCheck_1170_ = !lean_is_exclusive(v_code_996_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1171_ = lean_ctor_get(v_code_996_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_code_996_, 0);
lean_dec(v_unused_1172_);
v___x_1162_ = v_code_996_;
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v_code_996_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v_a_1155_);
lean_ctor_set(v___x_1162_, 0, v_a_1151_);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1151_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1155_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1165_);
v___x_1167_ = v___x_1157_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v___x_1174_; 
lean_dec(v_a_1155_);
lean_dec(v_a_1151_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_code_996_);
v___x_1174_ = v___x_1157_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_code_996_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
else
{
lean_dec(v_a_1151_);
lean_dec_ref(v_code_996_);
return v___x_1154_;
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v_code_996_);
v_a_1183_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1150_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1150_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
case 4:
{
lean_object* v_cases_1191_; lean_object* v_typeName_1192_; lean_object* v_resultType_1193_; lean_object* v_discr_1194_; lean_object* v_alts_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1234_; 
v_cases_1191_ = lean_ctor_get(v_code_996_, 0);
lean_inc_ref(v_cases_1191_);
v_typeName_1192_ = lean_ctor_get(v_cases_1191_, 0);
v_resultType_1193_ = lean_ctor_get(v_cases_1191_, 1);
v_discr_1194_ = lean_ctor_get(v_cases_1191_, 2);
v_alts_1195_ = lean_ctor_get(v_cases_1191_, 3);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_cases_1191_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1197_ = v_cases_1191_;
v_isShared_1198_ = v_isSharedCheck_1234_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_alts_1195_);
lean_inc(v_discr_1194_);
lean_inc(v_resultType_1193_);
lean_inc(v_typeName_1192_);
lean_dec(v_cases_1191_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1234_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1195_);
v___x_1200_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v___x_1199_, v_alts_1195_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1225_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1225_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1225_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
size_t v___x_1205_; size_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_ptr_addr(v_alts_1195_);
lean_dec_ref(v_alts_1195_);
v___x_1206_ = lean_ptr_addr(v_a_1201_);
v___x_1207_ = lean_usize_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1220_; 
v_isSharedCheck_1220_ = !lean_is_exclusive(v_code_996_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_code_996_, 0);
lean_dec(v_unused_1221_);
v___x_1209_ = v_code_996_;
v_isShared_1210_ = v_isSharedCheck_1220_;
goto v_resetjp_1208_;
}
else
{
lean_dec(v_code_996_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1220_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 3, v_a_1201_);
v___x_1212_ = v___x_1197_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_typeName_1192_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_resultType_1193_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_discr_1194_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_a_1201_);
v___x_1212_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1214_);
v___x_1216_ = v___x_1203_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_a_1201_);
lean_del_object(v___x_1197_);
lean_dec(v_discr_1194_);
lean_dec_ref(v_resultType_1193_);
lean_dec(v_typeName_1192_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v_code_996_);
v___x_1223_ = v___x_1203_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_code_996_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_del_object(v___x_1197_);
lean_dec_ref(v_alts_1195_);
lean_dec(v_discr_1194_);
lean_dec_ref(v_resultType_1193_);
lean_dec(v_typeName_1192_);
lean_dec_ref(v_code_996_);
v_a_1226_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1200_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1200_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
default: 
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_code_996_);
return v___x_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object* v_funDecl_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_params_1245_; lean_object* v_type_1246_; lean_object* v_value_1247_; uint8_t v___x_1248_; lean_object* v___y_1250_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_params_1245_ = lean_ctor_get(v_funDecl_1236_, 2);
lean_inc_ref(v_params_1245_);
v_type_1246_ = lean_ctor_get(v_funDecl_1236_, 3);
lean_inc_ref(v_type_1246_);
v_value_1247_ = lean_ctor_get(v_funDecl_1236_, 4);
v___x_1248_ = 0;
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_array_get_size(v_params_1245_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_inc_ref(v_value_1247_);
v___x_1264_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1247_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
v___y_1250_ = v___x_1264_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
if (v___x_1265_ == 0)
{
if (v___x_1263_ == 0)
{
lean_object* v___x_1266_; 
lean_inc_ref(v_value_1247_);
v___x_1266_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1247_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
v___y_1250_ = v___x_1266_;
goto v___jp_1249_;
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = ((size_t)0ULL);
v___x_1268_ = lean_usize_of_nat(v___x_1262_);
lean_inc(v_a_1239_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1245_, v___x_1267_, v___x_1268_, v_a_1239_);
lean_inc_ref(v_value_1247_);
v___x_1270_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1247_, v_a_1237_, v_a_1238_, v___x_1269_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v___x_1269_);
v___y_1250_ = v___x_1270_;
goto v___jp_1249_;
}
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1262_);
lean_inc(v_a_1239_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1245_, v___x_1271_, v___x_1272_, v_a_1239_);
lean_inc_ref(v_value_1247_);
v___x_1274_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_value_1247_, v_a_1237_, v_a_1238_, v___x_1273_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v___x_1273_);
v___y_1250_ = v___x_1274_;
goto v___jp_1249_;
}
}
v___jp_1249_:
{
if (lean_obj_tag(v___y_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; 
v_a_1251_ = lean_ctor_get(v___y_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___y_1250_);
v___x_1252_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1248_, v_funDecl_1236_, v_type_1246_, v_params_1245_, v_a_1251_, v_a_1241_);
return v___x_1252_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_type_1246_);
lean_dec_ref(v_params_1245_);
lean_dec_ref(v_funDecl_1236_);
v_a_1253_ = lean_ctor_get(v___y_1250_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___y_1250_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___y_1250_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___y_1250_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl___boxed(lean_object* v_funDecl_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(v_funDecl_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3___boxed(lean_object* v_i_1285_, lean_object* v_as_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v_i_1285_, v_as_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed(lean_object* v_code_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(v_code_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1305_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(lean_object* v_00_u03b2_1306_, lean_object* v_k_1307_, lean_object* v_t_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_1307_, v_t_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___boxed(lean_object* v_00_u03b2_1310_, lean_object* v_k_1311_, lean_object* v_t_1312_){
_start:
{
uint8_t v_res_1313_; lean_object* v_r_1314_; 
v_res_1313_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(v_00_u03b2_1310_, v_k_1311_, v_t_1312_);
lean_dec(v_t_1312_);
lean_dec(v_k_1311_);
v_r_1314_ = lean_box(v_res_1313_);
return v_r_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(lean_object* v_f_1315_, lean_object* v_v_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
if (lean_obj_tag(v_v_1316_) == 0)
{
lean_object* v_code_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1349_; 
v_code_1325_ = lean_ctor_get(v_v_1316_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_v_1316_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1327_ = v_v_1316_;
v_isShared_1328_ = v_isSharedCheck_1349_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_code_1325_);
lean_dec(v_v_1316_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1349_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; 
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
v___x_1329_ = lean_apply_9(v_f_1315_, v_code_1325_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, lean_box(0));
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1340_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1340_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1340_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_a_1330_);
v___x_1335_ = v___x_1327_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1335_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_del_object(v___x_1327_);
v_a_1341_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1329_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1329_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
else
{
lean_object* v___x_1350_; 
lean_dec_ref(v_f_1315_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_v_1316_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg___boxed(lean_object* v_f_1351_, lean_object* v_v_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1351_, v_v_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(uint8_t v_pu_1362_, lean_object* v_f_1363_, lean_object* v_v_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_1363_, v_v_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___boxed(lean_object* v_pu_1374_, lean_object* v_f_1375_, lean_object* v_v_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v_pu_boxed_1385_; lean_object* v_res_1386_; 
v_pu_boxed_1385_ = lean_unbox(v_pu_1374_);
v_res_1386_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(v_pu_boxed_1385_, v_f_1375_, v_v_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object* v_decl_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_toSignature_1397_; lean_object* v_value_1398_; uint8_t v_recursive_1399_; lean_object* v_inlineAttr_x3f_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1441_; 
v_toSignature_1397_ = lean_ctor_get(v_decl_1388_, 0);
v_value_1398_ = lean_ctor_get(v_decl_1388_, 1);
v_recursive_1399_ = lean_ctor_get_uint8(v_decl_1388_, sizeof(void*)*3);
v_inlineAttr_x3f_1400_ = lean_ctor_get(v_decl_1388_, 2);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_decl_1388_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1402_ = v_decl_1388_;
v_isShared_1403_ = v_isSharedCheck_1441_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_inlineAttr_x3f_1400_);
lean_inc(v_value_1398_);
lean_inc(v_toSignature_1397_);
lean_dec(v_decl_1388_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1441_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___y_1405_; lean_object* v_params_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_params_1425_ = lean_ctor_get(v_toSignature_1397_, 3);
v___x_1426_ = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0));
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_array_get_size(v_params_1425_);
v___x_1429_ = lean_nat_dec_lt(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1426_, v_value_1398_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
v___y_1405_ = v___x_1430_;
goto v___jp_1404_;
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_nat_dec_le(v___x_1428_, v___x_1428_);
if (v___x_1431_ == 0)
{
if (v___x_1429_ == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1426_, v_value_1398_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
v___y_1405_ = v___x_1432_;
goto v___jp_1404_;
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1428_);
lean_inc(v_a_1391_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1425_, v___x_1433_, v___x_1434_, v_a_1391_);
v___x_1436_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1426_, v_value_1398_, v_a_1389_, v_a_1390_, v___x_1435_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v___x_1435_);
v___y_1405_ = v___x_1436_;
goto v___jp_1404_;
}
}
else
{
size_t v___x_1437_; size_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = lean_usize_of_nat(v___x_1428_);
lean_inc(v_a_1391_);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_1425_, v___x_1437_, v___x_1438_, v_a_1391_);
v___x_1440_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_1426_, v_value_1398_, v_a_1389_, v_a_1390_, v___x_1439_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v___x_1439_);
v___y_1405_ = v___x_1440_;
goto v___jp_1404_;
}
}
v___jp_1404_:
{
if (lean_obj_tag(v___y_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1416_; 
v_a_1406_ = lean_ctor_get(v___y_1405_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___y_1405_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1408_ = v___y_1405_;
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___y_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v_a_1406_);
v___x_1411_ = v___x_1402_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_toSignature_1397_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_a_1406_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_inlineAttr_x3f_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*3, v_recursive_1399_);
v___x_1411_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1402_);
lean_dec(v_inlineAttr_x3f_1400_);
lean_dec_ref(v_toSignature_1397_);
v_a_1417_ = lean_ctor_get(v___y_1405_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___y_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___y_1405_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___y_1405_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___boxed(lean_object* v_decl_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object* v_decl_1457_, uint8_t v_liftInstParamOnly_1458_, uint8_t v_allowEtaContraction_1459_, lean_object* v_suffix_1460_, uint8_t v_inheritInlineAttrs_1461_, lean_object* v_minSize_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_ctx_1471_; lean_object* v___x_1472_; 
v___x_1468_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1));
v___x_1469_ = lean_st_mk_ref(v___x_1468_);
v___x_1470_ = lean_box(1);
lean_inc_ref(v_decl_1457_);
v_ctx_1471_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ctx_1471_, 0, v_suffix_1460_);
lean_ctor_set(v_ctx_1471_, 1, v_decl_1457_);
lean_ctor_set(v_ctx_1471_, 2, v_minSize_1462_);
lean_ctor_set_uint8(v_ctx_1471_, sizeof(void*)*3, v_liftInstParamOnly_1458_);
lean_ctor_set_uint8(v_ctx_1471_, sizeof(void*)*3 + 1, v_inheritInlineAttrs_1461_);
lean_ctor_set_uint8(v_ctx_1471_, sizeof(void*)*3 + 2, v_allowEtaContraction_1459_);
v___x_1472_ = l_Lean_Compiler_LCNF_LambdaLifting_main(v_decl_1457_, v_ctx_1471_, v___x_1469_, v___x_1470_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_ctx_1471_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1483_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v_decls_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1477_ = lean_st_ref_get(v___x_1469_);
lean_dec(v___x_1469_);
v_decls_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc_ref(v_decls_1478_);
lean_dec(v___x_1477_);
v___x_1479_ = lean_array_push(v_decls_1478_, v_a_1473_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1479_);
v___x_1481_ = v___x_1475_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v___x_1469_);
v_a_1484_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1472_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1472_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object* v_decl_1492_, lean_object* v_liftInstParamOnly_1493_, lean_object* v_allowEtaContraction_1494_, lean_object* v_suffix_1495_, lean_object* v_inheritInlineAttrs_1496_, lean_object* v_minSize_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
uint8_t v_liftInstParamOnly_boxed_1503_; uint8_t v_allowEtaContraction_boxed_1504_; uint8_t v_inheritInlineAttrs_boxed_1505_; lean_object* v_res_1506_; 
v_liftInstParamOnly_boxed_1503_ = lean_unbox(v_liftInstParamOnly_1493_);
v_allowEtaContraction_boxed_1504_ = lean_unbox(v_allowEtaContraction_1494_);
v_inheritInlineAttrs_boxed_1505_ = lean_unbox(v_inheritInlineAttrs_1496_);
v_res_1506_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v_decl_1492_, v_liftInstParamOnly_boxed_1503_, v_allowEtaContraction_boxed_1504_, v_suffix_1495_, v_inheritInlineAttrs_boxed_1505_, v_minSize_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(lean_object* v_as_1510_, size_t v_i_1511_, size_t v_stop_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_a_1520_; uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_eq(v_i_1511_, v_stop_1512_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = lean_array_uget_borrowed(v_as_1510_, v_i_1511_);
v___x_1527_ = 1;
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1));
lean_inc(v___x_1526_);
v___x_1529_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v___x_1526_, v___x_1524_, v___x_1527_, v___x_1528_, v___x_1524_, v___x_1525_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = l_Array_append___redArg(v_b_1513_, v_a_1530_);
lean_dec(v_a_1530_);
v_a_1520_ = v___x_1531_;
goto v___jp_1519_;
}
else
{
lean_dec_ref(v_b_1513_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1529_);
v_a_1520_ = v_a_1532_;
goto v___jp_1519_;
}
else
{
return v___x_1529_;
}
}
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_b_1513_);
return v___x_1533_;
}
v___jp_1519_:
{
size_t v___x_1521_; size_t v___x_1522_; 
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1511_, v___x_1521_);
v_i_1511_ = v___x_1522_;
v_b_1513_ = v_a_1520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object* v_as_1534_, lean_object* v_i_1535_, lean_object* v_stop_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
size_t v_i_boxed_1543_; size_t v_stop_boxed_1544_; lean_object* v_res_1545_; 
v_i_boxed_1543_ = lean_unbox_usize(v_i_1535_);
lean_dec(v_i_1535_);
v_stop_boxed_1544_ = lean_unbox_usize(v_stop_1536_);
lean_dec(v_stop_1536_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_as_1534_, v_i_boxed_1543_, v_stop_boxed_1544_, v_b_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_as_1534_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object* v___x_1546_, lean_object* v_decls_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1553_ = lean_mk_empty_array_with_capacity(v___x_1546_);
v___x_1554_ = lean_array_get_size(v_decls_1547_);
v___x_1555_ = lean_nat_dec_lt(v___x_1546_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1553_);
return v___x_1556_;
}
else
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_le(v___x_1554_, v___x_1554_);
if (v___x_1557_ == 0)
{
if (v___x_1555_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1553_);
return v___x_1558_;
}
else
{
size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = lean_usize_of_nat(v___x_1554_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_1547_, v___x_1559_, v___x_1560_, v___x_1553_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1561_;
}
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1554_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_1547_, v___x_1562_, v___x_1563_, v___x_1553_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object* v___x_1565_, lean_object* v_decls_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(v___x_1565_, v_decls_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_decls_1566_);
lean_dec(v___x_1565_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object* v_declName_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; lean_object* v_env_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1588_ = lean_st_ref_get(v___y_1586_);
v_env_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc_ref(v_env_1589_);
lean_dec(v___x_1588_);
v___x_1590_ = l_Lean_isImplicitReducibleCore(v_env_1589_, v_declName_1585_);
v___x_1591_ = lean_box(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object* v_declName_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1593_, v___y_1594_);
lean_dec(v___y_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object* v_declName_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_declName_1597_, v___y_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object* v_declName_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(v_declName_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(lean_object* v_as_1614_, size_t v_i_1615_, size_t v_stop_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_a_1624_; uint8_t v___x_1628_; 
v___x_1628_ = lean_usize_dec_eq(v_i_1615_, v_stop_1616_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v_toSignature_1630_; lean_object* v_name_1631_; lean_object* v___x_1632_; 
v___x_1629_ = lean_array_uget_borrowed(v_as_1614_, v_i_1615_);
v_toSignature_1630_ = lean_ctor_get(v___x_1629_, 0);
v_name_1631_ = lean_ctor_get(v_toSignature_1630_, 0);
lean_inc(v_name_1631_);
v___x_1632_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_name_1631_, v___y_1621_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; uint8_t v___y_1636_; uint8_t v___x_1644_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1632_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1644_ = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(v___x_1629_);
if (v___x_1644_ == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_unbox(v_a_1633_);
lean_dec(v_a_1633_);
v___y_1636_ = v___x_1645_;
goto v___jp_1635_;
}
else
{
lean_dec(v_a_1633_);
v___y_1636_ = v___x_1644_;
goto v___jp_1635_;
}
v___jp_1635_:
{
if (v___y_1636_ == 0)
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = 1;
v___x_1638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1));
lean_inc(v___x_1629_);
v___x_1639_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(v___x_1629_, v___x_1637_, v___x_1628_, v___x_1638_, v___x_1628_, v___x_1634_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = l_Array_append___redArg(v_b_1617_, v_a_1640_);
lean_dec(v_a_1640_);
v_a_1624_ = v___x_1641_;
goto v___jp_1623_;
}
else
{
lean_dec_ref(v_b_1617_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1642_; 
v_a_1642_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1639_);
v_a_1624_ = v_a_1642_;
goto v___jp_1623_;
}
else
{
return v___x_1639_;
}
}
}
else
{
lean_object* v___x_1643_; 
lean_inc(v___x_1629_);
v___x_1643_ = lean_array_push(v_b_1617_, v___x_1629_);
v_a_1624_ = v___x_1643_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_b_1617_);
v_a_1646_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1632_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1632_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_b_1617_);
return v___x_1654_;
}
v___jp_1623_:
{
size_t v___x_1625_; size_t v___x_1626_; 
v___x_1625_ = ((size_t)1ULL);
v___x_1626_ = lean_usize_add(v_i_1615_, v___x_1625_);
v_i_1615_ = v___x_1626_;
v_b_1617_ = v_a_1624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___boxed(lean_object* v_as_1655_, lean_object* v_i_1656_, lean_object* v_stop_1657_, lean_object* v_b_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
size_t v_i_boxed_1664_; size_t v_stop_boxed_1665_; lean_object* v_res_1666_; 
v_i_boxed_1664_ = lean_unbox_usize(v_i_1656_);
lean_dec(v_i_1656_);
v_stop_boxed_1665_ = lean_unbox_usize(v_stop_1657_);
lean_dec(v_stop_1657_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_as_1655_, v_i_boxed_1664_, v_stop_boxed_1665_, v_b_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_as_1655_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object* v___x_1667_, lean_object* v_decls_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1674_ = lean_mk_empty_array_with_capacity(v___x_1667_);
v___x_1675_ = lean_array_get_size(v_decls_1668_);
v___x_1676_ = lean_nat_dec_lt(v___x_1667_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1674_);
return v___x_1677_;
}
else
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_nat_dec_le(v___x_1675_, v___x_1675_);
if (v___x_1678_ == 0)
{
if (v___x_1676_ == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1674_);
return v___x_1679_;
}
else
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = lean_usize_of_nat(v___x_1675_);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_1668_, v___x_1680_, v___x_1681_, v___x_1674_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1682_;
}
}
else
{
size_t v___x_1683_; size_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((size_t)0ULL);
v___x_1684_ = lean_usize_of_nat(v___x_1675_);
v___x_1685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_1668_, v___x_1683_, v___x_1684_, v___x_1674_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object* v___x_1686_, lean_object* v_decls_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(v___x_1686_, v_decls_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec_ref(v_decls_1687_);
lean_dec(v___x_1686_);
return v_res_1693_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_unsigned_to_nat(4205464346u);
v___x_1762_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1763_ = l_Lean_Name_num___override(v___x_1762_, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1766_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1767_ = l_Lean_Name_str___override(v___x_1766_, v___x_1765_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1770_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1771_ = l_Lean_Name_str___override(v___x_1770_, v___x_1769_);
return v___x_1771_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_unsigned_to_nat(2u);
v___x_1773_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1774_ = l_Lean_Name_num___override(v___x_1773_, v___x_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1780_ = 1;
v___x_1781_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
v___x_1782_ = l_Lean_registerTraceClass(v___x_1779_, v___x_1780_, v___x_1781_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec_ref(v___x_1782_);
v___x_1783_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
v___x_1784_ = l_Lean_registerTraceClass(v___x_1783_, v___x_1780_, v___x_1781_);
return v___x_1784_;
}
else
{
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
return v_res_1786_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Level(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
