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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0_value;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_lam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_elam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 56, 62, 57, 79, 158, 214, 10)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineable___redArg(lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 70, 220, 104, 162, 210, 125, 97)}};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
x_9 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = 1;
if (lean_obj_tag(x_11) == 0)
{
if (x_6 == 0)
{
size_t x_13; size_t x_14; 
lean_free_object(x_9);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_box(x_12);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_11);
x_17 = lean_box(x_12);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = 1;
if (lean_obj_tag(x_18) == 0)
{
if (x_6 == 0)
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(x_19);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_18);
x_25 = lean_box(x_19);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
x_17 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(x_7, x_15, x_16, x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(x_1, x_2, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_10 = lean_ctor_get(x_2, 2);
x_11 = 0;
x_12 = l_Lean_Compiler_LCNF_Code_size(x_11, x_8);
x_13 = lean_nat_dec_lt(x_12, x_10);
lean_dec(x_12);
if (x_13 == 0)
{
if (x_9 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(x_1, x_3, x_4, x_5, x_6);
return x_17;
}
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_take(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_7, 1, x_11);
x_12 = lean_st_ref_set(x_2, x_7);
x_13 = l_Lean_Compiler_LCNF_getPhase___redArg(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_19 = lean_name_append_index_after(x_17, x_9);
lean_inc(x_18);
x_20 = l_Lean_Name_append(x_18, x_19);
x_21 = lean_unbox(x_16);
lean_dec(x_16);
lean_inc(x_20);
x_22 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_20, x_21, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 1)
{
lean_dec_ref(x_24);
lean_free_object(x_22);
lean_dec(x_20);
goto _start;
}
else
{
lean_dec(x_24);
lean_dec_ref(x_1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 1)
{
lean_dec_ref(x_26);
lean_dec(x_20);
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_20);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_set(x_2, x_39);
x_41 = l_Lean_Compiler_LCNF_getPhase___redArg(x_3);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec_ref(x_41);
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_47 = lean_name_append_index_after(x_45, x_36);
lean_inc(x_46);
x_48 = l_Lean_Name_append(x_46, x_47);
x_49 = lean_unbox(x_44);
lean_dec(x_44);
lean_inc(x_48);
x_50 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_48, x_49, x_4, x_5);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_obj_tag(x_51) == 1)
{
lean_dec_ref(x_51);
lean_dec(x_52);
lean_dec(x_48);
goto _start;
}
else
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec_ref(x_1);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_48);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_48);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_56 = x_50;
} else {
 lean_dec_ref(x_50);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_59 = x_41;
} else {
 lean_dec_ref(x_41);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(x_1, x_2, x_4, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_st_ref_take(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = 0;
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_2);
lean_inc_ref(x_12);
x_13 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_11, x_10, x_12);
lean_ctor_set(x_8, 0, x_13);
x_14 = lean_st_ref_set(x_3, x_8);
x_15 = 1;
x_16 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_11, x_1, x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec_ref(x_12);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = 0;
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_7);
lean_ctor_set(x_26, 3, x_2);
lean_inc_ref(x_26);
x_27 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_25, x_23, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_st_ref_set(x_3, x_28);
x_30 = 1;
x_31 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_25, x_1, x_30, x_3);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_32 = x_31;
} else {
 lean_dec_ref(x_31);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_26);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_2, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_array_size(x_1);
x_13 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(x_12, x_13, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_array_size(x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(x_18, x_13, x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_22 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_21, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_23);
x_24 = l_Lean_Compiler_LCNF_Code_inferType(x_21, x_23, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Array_append___redArg(x_15, x_20);
lean_dec(x_20);
lean_inc_ref(x_26);
x_27 = l_Lean_Compiler_LCNF_mkForallParams(x_21, x_26, x_25, x_7, x_8, x_9, x_10);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_23);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_4);
x_33 = 0;
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_33);
x_35 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_34);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_23);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_4);
x_40 = 0;
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_5);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
x_42 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_26);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
return x_24;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
return x_22;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_22, 0);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
lean_dec(x_19);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_14, 0);
lean_inc(x_57);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_mkLevelParam(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_mkLevelParam(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
lean_inc_ref(x_3);
x_20 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(x_3, x_4, x_5, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_73; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_73 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_box(0);
x_22 = x_74;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_3, 1);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
x_22 = x_76;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = lean_box(0);
goto block_72;
}
block_72:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1);
x_32 = lean_st_mk_ref(x_31);
x_33 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_23);
x_34 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
lean_dec_ref(x_34);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_32);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(x_1, x_2, x_21, x_35, x_22, x_32, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_st_ref_get(x_32);
lean_dec(x_32);
lean_dec(x_38);
x_39 = lean_ctor_get(x_37, 0);
x_40 = 0;
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_37);
x_41 = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(x_40, x_37, x_27, x_28);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_box(0);
lean_inc(x_44);
x_46 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(x_44, x_45);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_47; 
lean_inc(x_43);
lean_inc(x_26);
lean_inc(x_37);
x_47 = l_Lean_Compiler_LCNF_Decl_save(x_40, x_37, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_47);
x_48 = lean_st_ref_take(x_24);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_dec(x_51);
x_52 = lean_array_push(x_50, x_37);
lean_ctor_set(x_48, 1, x_30);
lean_ctor_set(x_48, 0, x_52);
x_53 = lean_st_ref_set(x_24, x_48);
x_10 = x_46;
x_11 = x_43;
x_12 = x_26;
x_13 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_array_push(x_54, x_37);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_30);
x_57 = lean_st_ref_set(x_24, x_56);
x_10 = x_46;
x_11 = x_43;
x_12 = x_26;
x_13 = lean_box(0);
goto block_19;
}
}
else
{
uint8_t x_58; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_37);
lean_dec(x_26);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
lean_dec_ref(x_42);
lean_inc(x_26);
x_62 = l_Lean_Compiler_LCNF_eraseDecl(x_40, x_37, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_10 = x_46;
x_11 = x_61;
x_12 = x_26;
x_13 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_63; 
lean_dec(x_61);
lean_dec(x_46);
lean_dec(x_26);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_41);
if (x_66 == 0)
{
return x_41;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_41, 0);
lean_inc(x_67);
lean_dec(x_41);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_36);
if (x_69 == 0)
{
return x_36;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_36, 0);
lean_inc(x_70);
lean_dec(x_36);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_20);
if (x_77 == 0)
{
return x_20;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
lean_dec(x_20);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
block_19:
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_size(x_1);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(x_14, x_15, x_1);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_2, x_17, x_12);
lean_dec(x_12);
lean_dec_ref(x_2);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_12, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_ctor_set(x_4, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
uint8_t x_17; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_array_fget(x_11, x_12);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_24);
if (lean_obj_tag(x_21) == 1)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_instBEqFVarId_beq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
lean_ctor_set(x_4, 0, x_29);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
else
{
size_t x_30; size_t x_31; 
lean_free_object(x_21);
lean_ctor_set(x_4, 0, x_14);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = l_Lean_instBEqFVarId_beq(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_4);
return x_37;
}
else
{
size_t x_38; size_t x_39; 
lean_ctor_set(x_4, 0, x_14);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
goto _start;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
lean_dec(x_21);
x_41 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
lean_ctor_set(x_4, 0, x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_4);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
x_43 = lean_array_uget(x_1, x_3);
x_44 = lean_array_fget(x_11, x_12);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_12, x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_13);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l_Lean_instBEqFVarId_beq(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_52);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_49;
 lean_ctor_set_tag(x_53, 0);
}
lean_ctor_set(x_53, 0, x_4);
return x_53;
}
else
{
size_t x_54; size_t x_55; 
lean_dec(x_49);
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_14);
x_54 = 1;
x_55 = lean_usize_add(x_3, x_54);
x_3 = x_55;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_43);
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_57);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_4);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 0);
x_61 = lean_ctor_get(x_59, 1);
x_62 = lean_ctor_get(x_59, 2);
x_63 = lean_box(0);
x_64 = lean_nat_dec_lt(x_61, x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_59);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_62);
lean_inc(x_61);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
x_68 = lean_array_uget(x_1, x_3);
x_69 = lean_array_fget(x_60, x_61);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_61, x_70);
lean_dec(x_61);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 3, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_62);
if (lean_obj_tag(x_68) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
lean_dec(x_69);
x_76 = l_Lean_instBEqFVarId_beq(x_73, x_75);
lean_dec(x_75);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_74;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; size_t x_81; size_t x_82; 
lean_dec(x_74);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_63);
lean_ctor_set(x_80, 1, x_72);
x_81 = 1;
x_82 = lean_usize_add(x_3, x_81);
x_3 = x_82;
x_4 = x_80;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_69);
lean_dec(x_68);
x_84 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0));
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 3)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
if (lean_obj_tag(x_21) == 5)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec_ref(x_18);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_21, 0);
x_31 = l_Lean_instBEqFVarId_beq(x_24, x_30);
lean_dec(x_30);
lean_dec(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_19);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_32 = lean_box(0);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_array_get_size(x_29);
x_34 = lean_array_get_size(x_23);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_19);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_36 = lean_box(0);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
else
{
lean_object* x_37; 
lean_free_object(x_21);
x_37 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
lean_inc(x_27);
x_40 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_27, x_39, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_43; 
lean_free_object(x_40);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_23);
x_46 = l_Array_toSubarray___redArg(x_23, x_45, x_34);
x_47 = lean_box(0);
lean_ctor_set(x_17, 1, x_46);
lean_ctor_set(x_17, 0, x_47);
x_48 = lean_array_size(x_29);
x_49 = 0;
x_50 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_29, x_48, x_49, x_17);
lean_dec_ref(x_29);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_50);
x_54 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
lean_ctor_set(x_19, 2, x_54);
x_55 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_19, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_42, 0, x_57);
lean_ctor_set(x_55, 0, x_42);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set(x_42, 0, x_58);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_42);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_free_object(x_42);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_free_object(x_42);
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec_ref(x_53);
lean_ctor_set(x_50, 0, x_63);
return x_50;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
lean_dec(x_50);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
lean_ctor_set(x_19, 2, x_66);
x_67 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_19, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
lean_ctor_set(x_42, 0, x_68);
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_42);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_42);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_free_object(x_42);
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_65, 0);
lean_inc(x_74);
lean_dec_ref(x_65);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_free_object(x_42);
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_50);
if (x_76 == 0)
{
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_50, 0);
lean_inc(x_77);
lean_dec(x_50);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; 
lean_dec(x_42);
x_79 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_23);
x_80 = l_Array_toSubarray___redArg(x_23, x_79, x_34);
x_81 = lean_box(0);
lean_ctor_set(x_17, 1, x_80);
lean_ctor_set(x_17, 0, x_81);
x_82 = lean_array_size(x_29);
x_83 = 0;
x_84 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_29, x_82, x_83, x_17);
lean_dec_ref(x_29);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_86);
x_88 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
lean_ctor_set(x_19, 2, x_88);
x_89 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_19, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_90);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_95 = x_89;
} else {
 lean_dec_ref(x_89);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
lean_dec_ref(x_87);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 1, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_84, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_100 = x_84;
} else {
 lean_dec_ref(x_84);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; 
lean_dec(x_42);
lean_free_object(x_19);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_102 = lean_box(0);
lean_ctor_set(x_40, 0, x_102);
return x_40;
}
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_40, 0);
lean_inc(x_103);
lean_dec(x_40);
if (lean_obj_tag(x_103) == 1)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; lean_object* x_110; 
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_104 = x_103;
} else {
 lean_dec_ref(x_103);
 x_104 = lean_box(0);
}
x_105 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_23);
x_106 = l_Array_toSubarray___redArg(x_23, x_105, x_34);
x_107 = lean_box(0);
lean_ctor_set(x_17, 1, x_106);
lean_ctor_set(x_17, 0, x_107);
x_108 = lean_array_size(x_29);
x_109 = 0;
x_110 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_29, x_108, x_109, x_17);
lean_dec_ref(x_29);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_112);
x_114 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
lean_ctor_set(x_19, 2, x_114);
x_115 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_19, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_104;
}
lean_ctor_set(x_118, 0, x_116);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_104);
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_113, 0);
lean_inc(x_123);
lean_dec_ref(x_113);
if (lean_is_scalar(x_112)) {
 x_124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_124 = x_112;
}
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_104);
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_126 = x_110;
} else {
 lean_dec_ref(x_110);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_103);
lean_free_object(x_19);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_free_object(x_19);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_40);
if (x_130 == 0)
{
return x_40;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_40, 0);
lean_inc(x_131);
lean_dec(x_40);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_free_object(x_19);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_37);
if (x_133 == 0)
{
return x_37;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_37, 0);
lean_inc(x_134);
lean_dec(x_37);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_19, 0);
x_137 = lean_ctor_get(x_19, 1);
x_138 = lean_ctor_get(x_19, 2);
x_139 = lean_ctor_get(x_21, 0);
lean_inc(x_139);
lean_dec(x_21);
x_140 = l_Lean_instBEqFVarId_beq(x_24, x_139);
lean_dec(x_139);
lean_dec(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_free_object(x_19);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_array_get_size(x_138);
x_144 = lean_array_get_size(x_23);
x_145 = lean_nat_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_19);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
else
{
lean_object* x_148; 
x_148 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_unbox(x_149);
lean_dec(x_149);
lean_inc(x_136);
x_151 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_136, x_150, x_7, x_8);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_obj_tag(x_152) == 1)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; size_t x_158; size_t x_159; lean_object* x_160; 
lean_dec(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_23);
x_156 = l_Array_toSubarray___redArg(x_23, x_155, x_144);
x_157 = lean_box(0);
lean_ctor_set(x_17, 1, x_156);
lean_ctor_set(x_17, 0, x_157);
x_158 = lean_array_size(x_138);
x_159 = 0;
x_160 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_138, x_158, x_159, x_17);
lean_dec_ref(x_138);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
x_164 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
lean_ctor_set(x_19, 2, x_164);
x_165 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_19, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_154;
}
lean_ctor_set(x_168, 0, x_166);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 1, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_154);
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_154);
lean_free_object(x_19);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_1);
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
lean_dec_ref(x_163);
if (lean_is_scalar(x_162)) {
 x_174 = lean_alloc_ctor(0, 1, 0);
} else {
 x_174 = x_162;
}
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_154);
lean_free_object(x_19);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_1);
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_176 = x_160;
} else {
 lean_dec_ref(x_160);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_152);
lean_free_object(x_19);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_178 = lean_box(0);
if (lean_is_scalar(x_153)) {
 x_179 = lean_alloc_ctor(0, 1, 0);
} else {
 x_179 = x_153;
}
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_free_object(x_19);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_151, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_181 = x_151;
} else {
 lean_dec_ref(x_151);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_free_object(x_19);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_148, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_184 = x_148;
} else {
 lean_dec_ref(x_148);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
return x_185;
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_186 = lean_ctor_get(x_19, 0);
x_187 = lean_ctor_get(x_19, 1);
x_188 = lean_ctor_get(x_19, 2);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_19);
x_189 = lean_ctor_get(x_21, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_190 = x_21;
} else {
 lean_dec_ref(x_21);
 x_190 = lean_box(0);
}
x_191 = l_Lean_instBEqFVarId_beq(x_24, x_189);
lean_dec(x_189);
lean_dec(x_24);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_192 = lean_box(0);
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 1, 0);
} else {
 x_193 = x_190;
 lean_ctor_set_tag(x_193, 0);
}
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_array_get_size(x_188);
x_195 = lean_array_get_size(x_23);
x_196 = lean_nat_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_197 = lean_box(0);
if (lean_is_scalar(x_190)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_190;
 lean_ctor_set_tag(x_198, 0);
}
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
else
{
lean_object* x_199; 
lean_dec(x_190);
x_199 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec_ref(x_199);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
lean_inc(x_186);
x_202 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_186, x_201, x_7, x_8);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
if (lean_obj_tag(x_203) == 1)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; size_t x_209; size_t x_210; lean_object* x_211; 
lean_dec(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
x_206 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_23);
x_207 = l_Array_toSubarray___redArg(x_23, x_206, x_195);
x_208 = lean_box(0);
lean_ctor_set(x_17, 1, x_207);
lean_ctor_set(x_17, 0, x_208);
x_209 = lean_array_size(x_188);
x_210 = 0;
x_211 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_188, x_209, x_210, x_17);
lean_dec_ref(x_188);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_213);
x_215 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
x_216 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_216, 0, x_186);
lean_ctor_set(x_216, 1, x_187);
lean_ctor_set(x_216, 2, x_215);
x_217 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_216, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_205;
}
lean_ctor_set(x_220, 0, x_218);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_205);
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_223 = x_217;
} else {
 lean_dec_ref(x_217);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_205);
lean_dec(x_187);
lean_dec(x_186);
lean_dec_ref(x_1);
x_225 = lean_ctor_get(x_214, 0);
lean_inc(x_225);
lean_dec_ref(x_214);
if (lean_is_scalar(x_213)) {
 x_226 = lean_alloc_ctor(0, 1, 0);
} else {
 x_226 = x_213;
}
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_205);
lean_dec(x_187);
lean_dec(x_186);
lean_dec_ref(x_1);
x_227 = lean_ctor_get(x_211, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_228 = x_211;
} else {
 lean_dec_ref(x_211);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_203);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_230 = lean_box(0);
if (lean_is_scalar(x_204)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_204;
}
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_232 = lean_ctor_get(x_202, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_233 = x_202;
} else {
 lean_dec_ref(x_202);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_free_object(x_17);
lean_dec_ref(x_1);
x_235 = lean_ctor_get(x_199, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 x_236 = x_199;
} else {
 lean_dec_ref(x_199);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
return x_237;
}
}
}
}
}
else
{
lean_free_object(x_17);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_17, 1);
lean_inc(x_238);
lean_dec(x_17);
if (lean_obj_tag(x_238) == 5)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_239 = lean_ctor_get(x_1, 2);
x_240 = lean_ctor_get(x_18, 0);
lean_inc(x_240);
lean_dec_ref(x_18);
x_241 = lean_ctor_get(x_19, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_19, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_243);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_244 = x_19;
} else {
 lean_dec_ref(x_19);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_238, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_246 = x_238;
} else {
 lean_dec_ref(x_238);
 x_246 = lean_box(0);
}
x_247 = l_Lean_instBEqFVarId_beq(x_240, x_245);
lean_dec(x_245);
lean_dec(x_240);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_248 = lean_box(0);
if (lean_is_scalar(x_246)) {
 x_249 = lean_alloc_ctor(0, 1, 0);
} else {
 x_249 = x_246;
 lean_ctor_set_tag(x_249, 0);
}
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_250 = lean_array_get_size(x_243);
x_251 = lean_array_get_size(x_239);
x_252 = lean_nat_dec_eq(x_250, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_253 = lean_box(0);
if (lean_is_scalar(x_246)) {
 x_254 = lean_alloc_ctor(0, 1, 0);
} else {
 x_254 = x_246;
 lean_ctor_set_tag(x_254, 0);
}
lean_ctor_set(x_254, 0, x_253);
return x_254;
}
else
{
lean_object* x_255; 
lean_dec(x_246);
x_255 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
lean_inc(x_241);
x_258 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_241, x_257, x_7, x_8);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_260 = x_258;
} else {
 lean_dec_ref(x_258);
 x_260 = lean_box(0);
}
if (lean_obj_tag(x_259) == 1)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; size_t x_266; size_t x_267; lean_object* x_268; 
lean_dec(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_239);
x_263 = l_Array_toSubarray___redArg(x_239, x_262, x_251);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
x_266 = lean_array_size(x_243);
x_267 = 0;
x_268 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_243, x_266, x_267, x_265);
lean_dec_ref(x_243);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_270);
x_272 = lean_obj_once(&l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0, &l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0);
if (lean_is_scalar(x_244)) {
 x_273 = lean_alloc_ctor(3, 3, 0);
} else {
 x_273 = x_244;
}
lean_ctor_set(x_273, 0, x_241);
lean_ctor_set(x_273, 1, x_242);
lean_ctor_set(x_273, 2, x_272);
x_274 = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(x_1, x_273, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_261;
}
lean_ctor_set(x_277, 0, x_275);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 1, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_261);
x_279 = lean_ctor_get(x_274, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_261);
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_282 = lean_ctor_get(x_271, 0);
lean_inc(x_282);
lean_dec_ref(x_271);
if (lean_is_scalar(x_270)) {
 x_283 = lean_alloc_ctor(0, 1, 0);
} else {
 x_283 = x_270;
}
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_261);
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_284 = lean_ctor_get(x_268, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_285 = x_268;
} else {
 lean_dec_ref(x_268);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_259);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_287 = lean_box(0);
if (lean_is_scalar(x_260)) {
 x_288 = lean_alloc_ctor(0, 1, 0);
} else {
 x_288 = x_260;
}
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_289 = lean_ctor_get(x_258, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_290 = x_258;
} else {
 lean_dec_ref(x_258);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_1);
x_292 = lean_ctor_get(x_255, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_293 = x_255;
} else {
 lean_dec_ref(x_255);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_292);
return x_294;
}
}
}
}
else
{
lean_dec_ref(x_238);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_10 = lean_box(0);
goto block_13;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_FVarIdSet_insert(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_28; lean_object* x_29; 
x_14 = lean_array_fget_borrowed(x_2, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_14, 1);
x_33 = lean_ctor_get(x_14, 2);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get_size(x_32);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_33);
x_37 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_14);
x_39 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_14, x_38);
x_15 = x_39;
x_16 = lean_box(0);
goto block_27;
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_35, x_35);
if (x_43 == 0)
{
if (x_36 == 0)
{
lean_object* x_44; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_33);
x_44 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_28 = x_45;
x_29 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_35);
lean_inc(x_5);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_32, x_49, x_50, x_5);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_33);
x_52 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_33, x_3, x_4, x_51, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_28 = x_53;
x_29 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_35);
lean_inc(x_5);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_32, x_57, x_58, x_5);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_33);
x_60 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_33, x_3, x_4, x_59, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_28 = x_61;
x_29 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_14, 0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_65);
x_66 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc_ref(x_14);
x_68 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_14, x_67);
x_15 = x_68;
x_16 = lean_box(0);
goto block_27;
}
else
{
uint8_t x_69; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
block_27:
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_14);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = lean_array_fset(x_2, x_1, x_15);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
lean_dec(x_1);
x_1 = x_25;
goto _start;
}
}
block_31:
{
lean_object* x_30; 
lean_inc(x_14);
x_30 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_14, x_28);
x_15 = x_30;
x_16 = lean_box(0);
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_Lean_FVarIdSet_insert(x_4, x_12);
lean_inc_ref(x_11);
x_14 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_11, x_2, x_3, x_13, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; size_t x_26; size_t x_27; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_26 = lean_ptr_addr(x_11);
x_27 = lean_ptr_addr(x_15);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
x_17 = x_28;
goto block_25;
}
else
{
size_t x_29; uint8_t x_30; 
x_29 = lean_ptr_addr(x_10);
x_30 = lean_usize_dec_eq(x_29, x_29);
x_17 = x_30;
goto block_25;
}
block_25:
{
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc_ref(x_10);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_15);
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_15);
if (lean_is_scalar(x_16)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_16;
}
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_15);
if (lean_is_scalar(x_16)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_16;
}
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
}
else
{
lean_dec_ref(x_1);
return x_14;
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_52; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_31);
x_52 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_53, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = l_Lean_FVarIdSet_insert(x_4, x_57);
lean_inc_ref(x_32);
x_59 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_32, x_2, x_3, x_58, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; size_t x_71; size_t x_72; uint8_t x_73; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_71 = lean_ptr_addr(x_32);
x_72 = lean_ptr_addr(x_60);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
x_62 = x_73;
goto block_70;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = lean_ptr_addr(x_31);
x_75 = lean_ptr_addr(x_53);
x_76 = lean_usize_dec_eq(x_74, x_75);
x_62 = x_76;
goto block_70;
}
block_70:
{
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_1, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_1, 0);
lean_dec(x_65);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_53);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_1);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_60);
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
lean_object* x_69; 
lean_dec(x_60);
lean_dec(x_53);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_1);
return x_69;
}
}
}
else
{
lean_dec(x_53);
lean_dec_ref(x_1);
return x_59;
}
}
else
{
lean_object* x_77; 
lean_inc_ref(x_32);
lean_dec_ref(x_1);
lean_inc(x_53);
x_77 = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
if (lean_obj_tag(x_78) == 1)
{
lean_object* x_79; 
lean_dec(x_55);
lean_dec(x_53);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_33 = x_79;
x_34 = x_2;
x_35 = x_3;
x_36 = x_4;
x_37 = x_5;
x_38 = x_6;
x_39 = x_7;
x_40 = x_8;
x_41 = lean_box(0);
goto block_51;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_78);
lean_inc(x_4);
x_80 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_80, 0, x_4);
x_81 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_81, 0, x_55);
lean_inc(x_53);
x_82 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed), 8, 1);
lean_closure_set(x_82, 0, x_53);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_83 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_82, x_80, x_81, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_87 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_86, x_53, x_2, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_33 = x_88;
x_34 = x_2;
x_35 = x_3;
x_36 = x_4;
x_37 = x_5;
x_38 = x_6;
x_39 = x_7;
x_40 = x_8;
x_41 = lean_box(0);
goto block_51;
}
else
{
uint8_t x_89; 
lean_dec_ref(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_53);
lean_dec_ref(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_92 = !lean_is_exclusive(x_83);
if (x_92 == 0)
{
return x_83;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
lean_dec(x_83);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_95 = !lean_is_exclusive(x_77);
if (x_95 == 0)
{
return x_77;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_77, 0);
lean_inc(x_96);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_53);
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_98 = !lean_is_exclusive(x_54);
if (x_98 == 0)
{
return x_54;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_54, 0);
lean_inc(x_99);
lean_dec(x_54);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_101 = !lean_is_exclusive(x_52);
if (x_101 == 0)
{
return x_52;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_52, 0);
lean_inc(x_102);
lean_dec(x_52);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
block_51:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = l_Lean_FVarIdSet_insert(x_36, x_42);
x_44 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_32, x_34, x_35, x_43, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_dec_ref(x_33);
return x_44;
}
}
}
case 2:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_1, 0);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_104);
x_106 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = l_Lean_FVarIdSet_insert(x_4, x_108);
lean_inc_ref(x_105);
x_110 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_105, x_2, x_3, x_109, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; size_t x_122; size_t x_123; uint8_t x_124; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_122 = lean_ptr_addr(x_105);
x_123 = lean_ptr_addr(x_111);
x_124 = lean_usize_dec_eq(x_122, x_123);
if (x_124 == 0)
{
x_113 = x_124;
goto block_121;
}
else
{
size_t x_125; size_t x_126; uint8_t x_127; 
x_125 = lean_ptr_addr(x_104);
x_126 = lean_ptr_addr(x_107);
x_127 = lean_usize_dec_eq(x_125, x_126);
x_113 = x_127;
goto block_121;
}
block_121:
{
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_1);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_1, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_1, 0);
lean_dec(x_116);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_107);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_1);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_1);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_111);
if (lean_is_scalar(x_112)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_112;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; 
lean_dec(x_111);
lean_dec(x_107);
if (lean_is_scalar(x_112)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_112;
}
lean_ctor_set(x_120, 0, x_1);
return x_120;
}
}
}
else
{
lean_dec(x_107);
lean_dec_ref(x_1);
return x_110;
}
}
else
{
uint8_t x_128; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_128 = !lean_is_exclusive(x_106);
if (x_128 == 0)
{
return x_106;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_106, 0);
lean_inc(x_129);
lean_dec(x_106);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
case 4:
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_131);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
x_135 = lean_ctor_get(x_131, 2);
x_136 = lean_ctor_get(x_131, 3);
x_137 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_136);
x_138 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(x_137, x_136, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; size_t x_141; size_t x_142; uint8_t x_143; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ptr_addr(x_136);
lean_dec_ref(x_136);
x_142 = lean_ptr_addr(x_140);
x_143 = lean_usize_dec_eq(x_141, x_142);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_1);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_1, 0);
lean_dec(x_145);
lean_ctor_set(x_131, 3, x_140);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
else
{
lean_object* x_146; 
lean_dec(x_1);
lean_ctor_set(x_131, 3, x_140);
x_146 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_146, 0, x_131);
lean_ctor_set(x_138, 0, x_146);
return x_138;
}
}
else
{
lean_dec(x_140);
lean_free_object(x_131);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
}
else
{
lean_object* x_147; size_t x_148; size_t x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
lean_dec(x_138);
x_148 = lean_ptr_addr(x_136);
lean_dec_ref(x_136);
x_149 = lean_ptr_addr(x_147);
x_150 = lean_usize_dec_eq(x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_151 = x_1;
} else {
 lean_dec_ref(x_1);
 x_151 = lean_box(0);
}
lean_ctor_set(x_131, 3, x_147);
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(4, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_131);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
else
{
lean_object* x_154; 
lean_dec(x_147);
lean_free_object(x_131);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_1);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_free_object(x_131);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_1);
x_155 = !lean_is_exclusive(x_138);
if (x_155 == 0)
{
return x_138;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_138, 0);
lean_inc(x_156);
lean_dec(x_138);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_131, 0);
x_159 = lean_ctor_get(x_131, 1);
x_160 = lean_ctor_get(x_131, 2);
x_161 = lean_ctor_get(x_131, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_131);
x_162 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_161);
x_163 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(x_162, x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_ptr_addr(x_161);
lean_dec_ref(x_161);
x_167 = lean_ptr_addr(x_164);
x_168 = lean_usize_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_169 = x_1;
} else {
 lean_dec_ref(x_1);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_170, 0, x_158);
lean_ctor_set(x_170, 1, x_159);
lean_ctor_set(x_170, 2, x_160);
lean_ctor_set(x_170, 3, x_164);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(4, 1, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
if (lean_is_scalar(x_165)) {
 x_172 = lean_alloc_ctor(0, 1, 0);
} else {
 x_172 = x_165;
}
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_164);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
if (lean_is_scalar(x_165)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_165;
}
lean_ctor_set(x_173, 0, x_1);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_163, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_175 = x_163;
} else {
 lean_dec_ref(x_163);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
}
default: 
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_1);
return x_177;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 4);
x_13 = 0;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_10);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_6);
lean_inc_ref(x_12);
x_24 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = x_24;
goto block_20;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_23 == 0)
{
lean_object* x_26; 
lean_inc(x_6);
lean_inc_ref(x_12);
x_26 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = x_26;
goto block_20;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_22);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_10, x_27, x_28, x_4);
lean_inc(x_6);
lean_inc_ref(x_12);
x_30 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_29, x_5, x_6, x_7, x_8);
x_14 = x_30;
goto block_20;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_22);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_10, x_31, x_32, x_4);
lean_inc(x_6);
lean_inc_ref(x_12);
x_34 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_33, x_5, x_6, x_7, x_8);
x_14 = x_34;
goto block_20;
}
}
block_20:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_13, x_1, x_11, x_10, x_15, x_6);
lean_dec(x_6);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_apply_9(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_9(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_28 = x_22;
} else {
 lean_dec_ref(x_22);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_26 = lean_ctor_get(x_10, 3);
x_27 = ((lean_object*)(l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0));
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_26);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(x_27, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = x_31;
goto block_25;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_29, x_29);
if (x_32 == 0)
{
if (x_30 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(x_27, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = x_33;
goto block_25;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_29);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_26, x_34, x_35, x_4);
x_37 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(x_27, x_11, x_2, x_3, x_36, x_5, x_6, x_7, x_8);
x_15 = x_37;
goto block_25;
}
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_29);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_26, x_38, x_39, x_4);
x_41 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(x_27, x_11, x_2, x_3, x_40, x_5, x_6, x_7, x_8);
x_15 = x_41;
goto block_25;
}
}
block_25:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_is_scalar(x_14)) {
 x_18 = lean_alloc_ctor(0, 3, 1);
} else {
 x_18 = x_14;
}
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 3, 1);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_12);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_10);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0, &l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1, &l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1);
x_13 = lean_st_mk_ref(x_12);
x_14 = lean_box(1);
lean_inc_ref(x_1);
x_15 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_3);
lean_inc(x_13);
x_16 = l_Lean_Compiler_LCNF_LambdaLifting_main(x_1, x_15, x_13, x_14, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_array_push(x_20, x_18);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = lean_array_push(x_24, x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Compiler_LCNF_Decl_lambdaLifting(x_1, x_12, x_13, x_4, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uget_borrowed(x_1, x_2);
x_19 = 1;
x_20 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_18);
x_21 = l_Lean_Compiler_LCNF_Decl_lambdaLifting(x_18, x_16, x_19, x_20, x_16, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Array_append___redArg(x_4, x_22);
lean_dec(x_22);
x_10 = x_23;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_10 = x_24;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_21;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
if (x_10 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(x_2, x_14, x_15, x_8, x_3, x_4, x_5, x_6);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(x_2, x_17, x_18, x_8, x_3, x_4, x_5, x_6);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_isImplicitReducibleCore(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget_borrowed(x_1, x_2);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(x_19, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_32; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(x_17);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = x_33;
goto block_31;
}
else
{
lean_dec(x_21);
x_23 = x_32;
goto block_31;
}
block_31:
{
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 1;
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_26 = l_Lean_Compiler_LCNF_Decl_lambdaLifting(x_17, x_24, x_16, x_25, x_16, x_22, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Array_append___redArg(x_4, x_27);
lean_dec(x_27);
x_10 = x_28;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
x_10 = x_29;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_26;
}
}
}
else
{
lean_object* x_30; 
lean_inc(x_17);
x_30 = lean_array_push(x_4, x_17);
x_10 = x_30;
x_11 = lean_box(0);
goto block_15;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_4);
return x_37;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
if (x_10 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(x_2, x_14, x_15, x_8, x_3, x_4, x_5, x_6);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(x_2, x_17, x_18, x_8, x_3, x_4, x_5, x_6);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4205464346u);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
x_3 = 1;
x_4 = lean_obj_once(&l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = ((lean_object*)(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_));
x_7 = l_Lean_registerTraceClass(x_6, x_3, x_4);
return x_7;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
return x_2;
}
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
if (builtin) {res = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
