// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceJpArity
// Imports: public import Lean.Compiler.LCNF.InferType
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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1_value;
static const lean_array_object l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceJpArity"};
static const lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 159, 49, 195, 174, 35, 168, 118)}};
static const lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 194, 75, 24, 236, 214, 183, 95)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ReduceJpArity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 30, 138, 61, 117, 158, 32, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(247, 202, 243, 145, 134, 14, 156, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 71, 137, 153, 8, 216, 125, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 239, 35, 247, 68, 251, 253, 157)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 2, 183, 133, 65, 4, 212, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 156, 123, 97, 186, 125, 28, 79)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 186, 51, 177, 148, 122, 241, 48)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 180, 182, 41, 102, 220, 202, 70)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 168, 162, 217, 66, 73, 237, 35)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 53, 57, 59, 209, 159, 92, 167)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 96, 72, 119, 107, 230, 50, 70)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)(((size_t)(563472653) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(212, 196, 129, 99, 150, 27, 32, 210)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 57, 146, 186, 53, 90, 0, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 247, 77, 12, 224, 72, 150, 173)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 155, 198, 21, 80, 165, 91, 81)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(lean_object* v_t_1_, lean_object* v_k_2_){
_start:
{
if (lean_obj_tag(v_t_1_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; uint8_t v___x_7_; 
v_k_3_ = lean_ctor_get(v_t_1_, 1);
v_v_4_ = lean_ctor_get(v_t_1_, 2);
v_l_5_ = lean_ctor_get(v_t_1_, 3);
v_r_6_ = lean_ctor_get(v_t_1_, 4);
v___x_7_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2_, v_k_3_);
switch(v___x_7_)
{
case 0:
{
v_t_1_ = v_l_5_;
goto _start;
}
case 1:
{
lean_object* v___x_9_; 
lean_inc(v_v_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_v_4_);
return v___x_9_;
}
default: 
{
v_t_1_ = v_r_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_t_12_, v_k_13_);
lean_dec(v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(lean_object* v_as_15_, size_t v_sz_16_, size_t v_i_17_, lean_object* v_b_18_){
_start:
{
lean_object* v_a_21_; uint8_t v___x_25_; 
v___x_25_ = lean_usize_dec_lt(v_i_17_, v_sz_16_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_b_18_);
return v___x_26_;
}
else
{
lean_object* v_snd_27_; lean_object* v_fst_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_62_; 
v_snd_27_ = lean_ctor_get(v_b_18_, 1);
v_fst_28_ = lean_ctor_get(v_b_18_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v_b_18_);
if (v_isSharedCheck_62_ == 0)
{
v___x_30_ = v_b_18_;
v_isShared_31_ = v_isSharedCheck_62_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_snd_27_);
lean_inc(v_fst_28_);
lean_dec(v_b_18_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_62_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_array_32_; lean_object* v_start_33_; lean_object* v_stop_34_; uint8_t v___x_35_; 
v_array_32_ = lean_ctor_get(v_snd_27_, 0);
v_start_33_ = lean_ctor_get(v_snd_27_, 1);
v_stop_34_ = lean_ctor_get(v_snd_27_, 2);
v___x_35_ = lean_nat_dec_lt(v_start_33_, v_stop_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_37_; 
if (v_isShared_31_ == 0)
{
v___x_37_ = v___x_30_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_fst_28_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_snd_27_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
else
{
lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_58_; 
lean_inc(v_stop_34_);
lean_inc(v_start_33_);
lean_inc_ref(v_array_32_);
v_isSharedCheck_58_ = !lean_is_exclusive(v_snd_27_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; lean_object* v_unused_60_; lean_object* v_unused_61_; 
v_unused_59_ = lean_ctor_get(v_snd_27_, 2);
lean_dec(v_unused_59_);
v_unused_60_ = lean_ctor_get(v_snd_27_, 1);
lean_dec(v_unused_60_);
v_unused_61_ = lean_ctor_get(v_snd_27_, 0);
lean_dec(v_unused_61_);
v___x_41_ = v_snd_27_;
v_isShared_42_ = v_isSharedCheck_58_;
goto v_resetjp_40_;
}
else
{
lean_dec(v_snd_27_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_58_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_a_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v_a_43_ = lean_array_uget_borrowed(v_as_15_, v_i_17_);
v___x_44_ = lean_array_fget(v_array_32_, v_start_33_);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_add(v_start_33_, v___x_45_);
lean_dec(v_start_33_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_46_);
v___x_48_ = v___x_41_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_array_32_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_57_, 2, v_stop_34_);
v___x_48_ = v_reuseFailAlloc_57_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
uint8_t v___x_49_; 
v___x_49_ = lean_unbox(v_a_43_);
if (v___x_49_ == 0)
{
lean_object* v___x_51_; 
lean_dec(v___x_44_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_48_);
v___x_51_ = v___x_30_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_fst_28_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_48_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_a_21_ = v___x_51_;
goto v___jp_20_;
}
}
else
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lean_array_push(v_fst_28_, v___x_44_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_48_);
lean_ctor_set(v___x_30_, 0, v___x_53_);
v___x_55_ = v___x_30_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_48_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
v_a_21_ = v___x_55_;
goto v___jp_20_;
}
}
}
}
}
}
}
v___jp_20_:
{
size_t v___x_22_; size_t v___x_23_; 
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_add(v_i_17_, v___x_22_);
v_i_17_ = v___x_23_;
v_b_18_ = v_a_21_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg___boxed(lean_object* v_as_63_, lean_object* v_sz_64_, lean_object* v_i_65_, lean_object* v_b_66_, lean_object* v___y_67_){
_start:
{
size_t v_sz_boxed_68_; size_t v_i_boxed_69_; lean_object* v_res_70_; 
v_sz_boxed_68_ = lean_unbox_usize(v_sz_64_);
lean_dec(v_sz_64_);
v_i_boxed_69_ = lean_unbox_usize(v_i_65_);
lean_dec(v_i_65_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_as_63_, v_sz_boxed_68_, v_i_boxed_69_, v_b_66_);
lean_dec_ref(v_as_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_m_71_, lean_object* v_query_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_zero_76_; uint8_t v_isZero_77_; 
v_zero_76_ = lean_unsigned_to_nat(0u);
v_isZero_77_ = lean_nat_dec_eq(v_x_74_, v_zero_76_);
if (v_isZero_77_ == 1)
{
lean_dec(v_x_75_);
lean_dec(v_x_74_);
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(2);
return v___x_78_;
}
else
{
lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_val_79_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v_x_73_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v_x_73_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_val_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
else
{
lean_object* v_keyArray_87_; lean_object* v_valueArray_88_; lean_object* v___x_89_; uint8_t v_isSome_90_; 
v_keyArray_87_ = lean_ctor_get(v_m_71_, 1);
v_valueArray_88_ = lean_ctor_get(v_m_71_, 2);
v___x_89_ = lean_array_fget_borrowed(v_keyArray_87_, v_x_75_);
v_isSome_90_ = lean_noption_is_some(v___x_89_);
if (v_isSome_90_ == 0)
{
lean_dec(v_x_74_);
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_x_75_);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v_x_75_);
v_val_92_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v_x_73_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_val_92_);
lean_dec(v_x_73_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_val_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
else
{
lean_object* v_one_100_; lean_object* v_n_101_; lean_object* v___y_103_; 
v_one_100_ = lean_unsigned_to_nat(1u);
v_n_101_ = lean_nat_sub(v_x_74_, v_one_100_);
lean_dec(v_x_74_);
if (v_isSome_90_ == 0)
{
goto v___jp_109_;
}
else
{
lean_object* v___x_111_; uint8_t v_isSome_112_; 
v___x_111_ = lean_array_fget_borrowed(v_valueArray_88_, v_x_75_);
v_isSome_112_ = lean_noption_is_some(v___x_111_);
if (v_isSome_112_ == 0)
{
goto v___jp_109_;
}
else
{
lean_object* v_val_113_; uint8_t v___x_114_; 
lean_inc(v___x_89_);
v_val_113_ = lean_noption_get(v___x_89_);
v___x_114_ = l_Lean_instBEqFVarId_beq(v_val_113_, v_query_72_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
lean_dec(v_val_113_);
v___x_115_ = lean_array_get_size(v_keyArray_87_);
v___x_116_ = lean_nat_add(v_x_75_, v_one_100_);
lean_dec(v_x_75_);
v___x_117_ = lean_nat_dec_lt(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
lean_dec(v___x_116_);
v_x_74_ = v_n_101_;
v_x_75_ = v_zero_76_;
goto _start;
}
else
{
v_x_74_ = v_n_101_;
v_x_75_ = v___x_116_;
goto _start;
}
}
else
{
lean_object* v_val_120_; lean_object* v___x_121_; 
lean_dec(v_n_101_);
lean_dec(v_x_73_);
lean_inc(v___x_111_);
v_val_120_ = lean_noption_get(v___x_111_);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v_x_75_);
lean_ctor_set(v___x_121_, 1, v_val_113_);
lean_ctor_set(v___x_121_, 2, v_val_120_);
return v___x_121_;
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_array_get_size(v_keyArray_87_);
v___x_105_ = lean_nat_add(v_x_75_, v_one_100_);
lean_dec(v_x_75_);
v___x_106_ = lean_nat_dec_lt(v___x_105_, v___x_104_);
if (v___x_106_ == 0)
{
lean_dec(v___x_105_);
v_x_73_ = v___y_103_;
v_x_74_ = v_n_101_;
v_x_75_ = v_zero_76_;
goto _start;
}
else
{
v_x_73_ = v___y_103_;
v_x_74_ = v_n_101_;
v_x_75_ = v___x_105_;
goto _start;
}
}
v___jp_109_:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_110_; 
lean_inc(v_x_75_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_x_75_);
v___y_103_ = v___x_110_;
goto v___jp_102_;
}
else
{
v___y_103_ = v_x_73_;
goto v___jp_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_m_122_, lean_object* v_query_123_, lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg(v_m_122_, v_query_123_, v_x_124_, v_x_125_, v_x_126_);
lean_dec(v_query_123_);
lean_dec_ref(v_m_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg(lean_object* v_m_128_, lean_object* v_query_129_){
_start:
{
lean_object* v_keyArray_130_; lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v_fold_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_keyArray_130_ = lean_ctor_get(v_m_128_, 1);
v___x_131_ = lean_array_get_size(v_keyArray_130_);
v___x_132_ = l_Lean_instHashableFVarId_hash(v_query_129_);
v___x_133_ = 32ULL;
v___x_134_ = lean_uint64_shift_right(v___x_132_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v___x_132_, v___x_134_);
v___x_136_ = 16ULL;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_131_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v___x_144_ = lean_usize_to_nat(v___x_143_);
v___x_145_ = lean_box(0);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg(v_m_128_, v_query_129_, v___x_145_, v___x_131_, v___x_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_147_, lean_object* v_query_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg(v_m_147_, v_query_148_);
lean_dec(v_query_148_);
lean_dec_ref(v_m_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(lean_object* v_m_150_, lean_object* v_query_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg(v_m_150_, v_query_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_index_153_; lean_object* v_key_154_; lean_object* v_value_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_index_153_ = lean_ctor_get(v___x_152_, 0);
v_key_154_ = lean_ctor_get(v___x_152_, 1);
v_value_155_ = lean_ctor_get(v___x_152_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_152_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_value_155_);
lean_inc(v_key_154_);
lean_inc(v_index_153_);
lean_dec(v___x_152_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_index_153_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_key_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_value_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v___x_163_; 
lean_dec(v___x_152_);
v___x_163_ = lean_box(1);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg___boxed(lean_object* v_m_164_, lean_object* v_query_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_m_164_, v_query_165_);
lean_dec(v_query_165_);
lean_dec_ref(v_m_164_);
return v_res_166_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object* v_m_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_m_167_, v_a_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
uint8_t v___x_170_; 
lean_dec_ref_known(v___x_169_, 3);
v___x_170_ = 1;
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object* v_m_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_m_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object* v_as_176_, size_t v_sz_177_, size_t v_i_178_, lean_object* v_b_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_a_183_; uint8_t v___x_187_; 
v___x_187_ = lean_usize_dec_lt(v_i_178_, v_sz_177_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_b_179_);
return v___x_188_;
}
else
{
lean_object* v_snd_189_; lean_object* v_fst_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_232_; 
v_snd_189_ = lean_ctor_get(v_b_179_, 1);
v_fst_190_ = lean_ctor_get(v_b_179_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_b_179_);
if (v_isSharedCheck_232_ == 0)
{
v___x_192_ = v_b_179_;
v_isShared_193_ = v_isSharedCheck_232_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snd_189_);
lean_inc(v_fst_190_);
lean_dec(v_b_179_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_232_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_231_; 
v_fst_194_ = lean_ctor_get(v_snd_189_, 0);
v_snd_195_ = lean_ctor_get(v_snd_189_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_snd_189_);
if (v_isSharedCheck_231_ == 0)
{
v___x_197_ = v_snd_189_;
v_isShared_198_ = v_isSharedCheck_231_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_snd_195_);
lean_inc(v_fst_194_);
lean_dec(v_snd_189_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_231_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_a_199_; lean_object* v_fvarId_200_; lean_object* v_type_201_; uint8_t v___x_202_; 
v_a_199_ = lean_array_uget_borrowed(v_as_176_, v_i_178_);
v_fvarId_200_ = lean_ctor_get(v_a_199_, 0);
v_type_201_ = lean_ctor_get(v_a_199_, 2);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_fst_190_, v_fvarId_200_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; lean_object* v___x_204_; 
v___x_203_ = 0;
v___x_204_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_203_, v_a_199_, v___y_180_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec_ref_known(v___x_204_, 1);
v___x_205_ = lean_box(v___x_202_);
v___x_206_ = lean_array_push(v_fst_194_, v___x_205_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_206_);
v___x_208_ = v___x_197_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_snd_195_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_208_);
v___x_210_ = v___x_192_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_fst_190_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_a_183_ = v___x_210_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_del_object(v___x_197_);
lean_dec(v_snd_195_);
lean_dec(v_fst_194_);
lean_del_object(v___x_192_);
lean_dec(v_fst_190_);
v_a_213_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_204_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_204_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
lean_inc_ref(v_type_201_);
v___x_221_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(v_type_201_, v_fst_190_);
v___x_222_ = lean_box(v___x_202_);
v___x_223_ = lean_array_push(v_fst_194_, v___x_222_);
lean_inc(v_a_199_);
v___x_224_ = lean_array_push(v_snd_195_, v_a_199_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_224_);
lean_ctor_set(v___x_197_, 0, v___x_223_);
v___x_226_ = v___x_197_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_224_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_226_);
lean_ctor_set(v___x_192_, 0, v___x_221_);
v___x_228_ = v___x_192_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_a_183_ = v___x_228_;
goto v___jp_182_;
}
}
}
}
}
}
v___jp_182_:
{
size_t v___x_184_; size_t v___x_185_; 
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_add(v_i_178_, v___x_184_);
v_i_178_ = v___x_185_;
v_b_179_ = v_a_183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object* v_as_233_, lean_object* v_sz_234_, lean_object* v_i_235_, lean_object* v_b_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
size_t v_sz_boxed_239_; size_t v_i_boxed_240_; lean_object* v_res_241_; 
v_sz_boxed_239_ = lean_unbox_usize(v_sz_234_);
lean_dec(v_sz_234_);
v_i_boxed_240_ = lean_unbox_usize(v_i_235_);
lean_dec(v_i_235_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_233_, v_sz_boxed_239_, v_i_boxed_240_, v_b_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v_as_233_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object* v_code_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
switch(lean_obj_tag(v_code_248_))
{
case 0:
{
lean_object* v_decl_255_; lean_object* v_k_256_; lean_object* v___x_257_; 
v_decl_255_ = lean_ctor_get(v_code_248_, 0);
v_k_256_ = lean_ctor_get(v_code_248_, 1);
lean_inc_ref(v_k_256_);
v___x_257_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_256_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_284_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_284_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_284_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_284_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___y_263_; size_t v___x_279_; size_t v___x_280_; uint8_t v___x_281_; 
v___x_279_ = lean_ptr_addr(v_k_256_);
v___x_280_ = lean_ptr_addr(v_a_258_);
v___x_281_ = lean_usize_dec_eq(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
v___y_263_ = v___x_281_;
goto v___jp_262_;
}
else
{
size_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_ptr_addr(v_decl_255_);
v___x_283_ = lean_usize_dec_eq(v___x_282_, v___x_282_);
v___y_263_ = v___x_283_;
goto v___jp_262_;
}
v___jp_262_:
{
if (v___y_263_ == 0)
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
lean_inc_ref(v_decl_255_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_code_248_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_274_ = lean_ctor_get(v_code_248_, 1);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_code_248_, 0);
lean_dec(v_unused_275_);
v___x_265_ = v_code_248_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_code_248_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_a_258_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_decl_255_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_a_258_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_268_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v___x_277_; 
lean_dec(v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v_code_248_);
v___x_277_ = v___x_260_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_code_248_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_248_, 2);
return v___x_257_;
}
}
case 1:
{
lean_object* v_decl_285_; lean_object* v_k_286_; lean_object* v_params_287_; lean_object* v_type_288_; lean_object* v_value_289_; lean_object* v___x_290_; 
v_decl_285_ = lean_ctor_get(v_code_248_, 0);
v_k_286_ = lean_ctor_get(v_code_248_, 1);
v_params_287_ = lean_ctor_get(v_decl_285_, 2);
v_type_288_ = lean_ctor_get(v_decl_285_, 3);
v_value_289_ = lean_ctor_get(v_decl_285_, 4);
lean_inc_ref(v_value_289_);
v___x_290_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_value_289_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; uint8_t v___x_292_; lean_object* v___x_293_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = 0;
lean_inc_ref(v_params_287_);
lean_inc_ref(v_type_288_);
lean_inc_ref(v_decl_285_);
v___x_293_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_292_, v_decl_285_, v_type_288_, v_params_287_, v_a_291_, v_a_251_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
lean_inc_ref(v_k_286_);
v___x_295_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_286_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_323_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_323_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_323_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_323_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint8_t v___y_301_; size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_ptr_addr(v_k_286_);
v___x_318_ = lean_ptr_addr(v_a_296_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
v___y_301_ = v___x_319_;
goto v___jp_300_;
}
else
{
size_t v___x_320_; size_t v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_ptr_addr(v_decl_285_);
v___x_321_ = lean_ptr_addr(v_a_294_);
v___x_322_ = lean_usize_dec_eq(v___x_320_, v___x_321_);
v___y_301_ = v___x_322_;
goto v___jp_300_;
}
v___jp_300_:
{
if (v___y_301_ == 0)
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v_code_248_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_code_248_, 1);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_code_248_, 0);
lean_dec(v_unused_313_);
v___x_303_ = v_code_248_;
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_code_248_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_a_296_);
lean_ctor_set(v___x_303_, 0, v_a_294_);
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_294_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_a_296_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_306_);
v___x_308_ = v___x_298_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v_a_296_);
lean_dec(v_a_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_code_248_);
v___x_315_ = v___x_298_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_code_248_);
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
else
{
lean_dec(v_a_294_);
lean_dec_ref_known(v_code_248_, 2);
return v___x_295_;
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref_known(v_code_248_, 2);
v_a_324_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_293_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_293_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_248_, 2);
return v___x_290_;
}
}
case 2:
{
lean_object* v_decl_332_; lean_object* v_k_333_; lean_object* v_params_334_; lean_object* v_type_335_; lean_object* v_value_336_; lean_object* v___x_337_; 
v_decl_332_ = lean_ctor_get(v_code_248_, 0);
v_k_333_ = lean_ctor_get(v_code_248_, 1);
v_params_334_ = lean_ctor_get(v_decl_332_, 2);
v_type_335_ = lean_ctor_get(v_decl_332_, 3);
v_value_336_ = lean_ctor_get(v_decl_332_, 4);
lean_inc_ref(v_value_336_);
v___x_337_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_value_336_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_n(v_a_338_, 2);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_340_ = 0;
v___x_341_ = l_Lean_Compiler_LCNF_Code_collectUsed(v___x_340_, v_a_338_, v___x_339_);
lean_inc_ref(v_params_334_);
v___x_342_ = l_Array_reverse___redArg(v_params_334_);
v___x_343_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1));
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v_sz_345_ = lean_array_size(v___x_342_);
v___x_346_ = ((size_t)0ULL);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v___x_342_, v_sz_345_, v___x_346_, v___x_344_, v_a_251_);
lean_dec_ref(v___x_342_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v_snd_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v_snd_349_ = lean_ctor_get(v_a_348_, 1);
lean_inc(v_snd_349_);
lean_dec(v_a_348_);
v_fst_350_ = lean_ctor_get(v_snd_349_, 0);
lean_inc(v_fst_350_);
v_snd_351_ = lean_ctor_get(v_snd_349_, 1);
lean_inc(v_snd_351_);
lean_dec(v_snd_349_);
v___x_352_ = l_Array_reverse___redArg(v_snd_351_);
v___x_353_ = lean_array_get_size(v___x_352_);
v___x_354_ = lean_array_get_size(v_params_334_);
v___x_355_ = lean_nat_dec_eq(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_404_; 
lean_inc_ref(v_k_333_);
lean_inc_ref(v_decl_332_);
v_isSharedCheck_404_ = !lean_is_exclusive(v_code_248_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_405_ = lean_ctor_get(v_code_248_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_code_248_, 0);
lean_dec(v_unused_406_);
v___x_357_ = v_code_248_;
v_isShared_358_ = v_isSharedCheck_404_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_code_248_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_404_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; 
lean_inc(v_a_338_);
v___x_359_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_340_, v_a_338_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
lean_inc_ref(v___x_352_);
v___x_361_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_340_, v___x_352_, v_a_360_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v___x_363_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_340_, v_decl_332_, v_a_362_, v___x_352_, v_a_338_, v_a_251_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v_fvarId_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v_fvarId_365_ = lean_ctor_get(v_a_364_, 0);
v___x_366_ = l_Array_reverse___redArg(v_fst_350_);
lean_inc(v_a_249_);
lean_inc(v_fvarId_365_);
v___x_367_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_365_, v___x_366_, v_a_249_);
v___x_368_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_333_, v___x_367_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_379_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_379_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_a_369_);
lean_ctor_set(v___x_357_, 0, v_a_364_);
v___x_374_ = v___x_357_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_364_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_a_369_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
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
else
{
lean_dec(v_a_364_);
lean_del_object(v___x_357_);
return v___x_368_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_del_object(v___x_357_);
lean_dec(v_fst_350_);
lean_dec_ref(v_k_333_);
v_a_380_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_363_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_363_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_del_object(v___x_357_);
lean_dec_ref(v___x_352_);
lean_dec(v_fst_350_);
lean_dec(v_a_338_);
lean_dec_ref(v_k_333_);
lean_dec_ref(v_decl_332_);
v_a_388_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_361_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_361_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_del_object(v___x_357_);
lean_dec_ref(v___x_352_);
lean_dec(v_fst_350_);
lean_dec(v_a_338_);
lean_dec_ref(v_k_333_);
lean_dec_ref(v_decl_332_);
v_a_396_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_359_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_359_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
else
{
lean_object* v___x_407_; 
lean_dec_ref(v___x_352_);
lean_dec(v_fst_350_);
lean_inc_ref(v_params_334_);
lean_inc_ref(v_type_335_);
lean_inc_ref(v_decl_332_);
v___x_407_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_340_, v_decl_332_, v_type_335_, v_params_334_, v_a_338_, v_a_251_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
lean_inc_ref(v_k_333_);
v___x_409_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_333_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_437_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_437_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_437_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_437_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___y_415_; size_t v___x_431_; size_t v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_ptr_addr(v_k_333_);
v___x_432_ = lean_ptr_addr(v_a_410_);
v___x_433_ = lean_usize_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
v___y_415_ = v___x_433_;
goto v___jp_414_;
}
else
{
size_t v___x_434_; size_t v___x_435_; uint8_t v___x_436_; 
v___x_434_ = lean_ptr_addr(v_decl_332_);
v___x_435_ = lean_ptr_addr(v_a_408_);
v___x_436_ = lean_usize_dec_eq(v___x_434_, v___x_435_);
v___y_415_ = v___x_436_;
goto v___jp_414_;
}
v___jp_414_:
{
if (v___y_415_ == 0)
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_425_; 
v_isSharedCheck_425_ = !lean_is_exclusive(v_code_248_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; 
v_unused_426_ = lean_ctor_get(v_code_248_, 1);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_code_248_, 0);
lean_dec(v_unused_427_);
v___x_417_ = v_code_248_;
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_code_248_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_a_410_);
lean_ctor_set(v___x_417_, 0, v_a_408_);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_a_410_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_420_);
v___x_422_ = v___x_412_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v___x_429_; 
lean_dec(v_a_410_);
lean_dec(v_a_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v_code_248_);
v___x_429_ = v___x_412_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_code_248_);
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
else
{
lean_dec(v_a_408_);
lean_dec_ref_known(v_code_248_, 2);
return v___x_409_;
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref_known(v_code_248_, 2);
v_a_438_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_407_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_407_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_a_338_);
lean_dec_ref_known(v_code_248_, 2);
v_a_446_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_347_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_347_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_248_, 2);
return v___x_337_;
}
}
case 3:
{
lean_object* v_fvarId_454_; lean_object* v_args_455_; lean_object* v___x_456_; 
v_fvarId_454_ = lean_ctor_get(v_code_248_, 0);
v_args_455_ = lean_ctor_get(v_code_248_, 1);
v___x_456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_a_249_, v_fvarId_454_);
if (lean_obj_tag(v___x_456_) == 1)
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_489_; 
lean_inc_ref(v_args_455_);
lean_inc(v_fvarId_454_);
v_isSharedCheck_489_ = !lean_is_exclusive(v_code_248_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; lean_object* v_unused_491_; 
v_unused_490_ = lean_ctor_get(v_code_248_, 1);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_code_248_, 0);
lean_dec(v_unused_491_);
v___x_458_ = v_code_248_;
v_isShared_459_ = v_isSharedCheck_489_;
goto v_resetjp_457_;
}
else
{
lean_dec(v_code_248_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_489_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_val_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; size_t v_sz_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_val_460_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v___x_456_, 1);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2));
v___x_463_ = lean_array_get_size(v_args_455_);
v___x_464_ = l_Array_toSubarray___redArg(v_args_455_, v___x_461_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_462_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v_sz_466_ = lean_array_size(v_val_460_);
v___x_467_ = ((size_t)0ULL);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_val_460_, v_sz_466_, v___x_467_, v___x_465_);
lean_dec(v_val_460_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_480_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_480_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_fst_473_; lean_object* v___x_475_; 
v_fst_473_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fst_473_);
lean_dec(v_a_469_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v_fst_473_);
v___x_475_ = v___x_458_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fvarId_454_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_fst_473_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_475_);
v___x_477_ = v___x_471_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_458_);
lean_dec(v_fvarId_454_);
v_a_481_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_468_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_468_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v___x_456_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v_code_248_);
return v___x_492_;
}
}
case 4:
{
lean_object* v_cases_493_; lean_object* v_typeName_494_; lean_object* v_resultType_495_; lean_object* v_discr_496_; lean_object* v_alts_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_536_; 
v_cases_493_ = lean_ctor_get(v_code_248_, 0);
lean_inc_ref(v_cases_493_);
v_typeName_494_ = lean_ctor_get(v_cases_493_, 0);
v_resultType_495_ = lean_ctor_get(v_cases_493_, 1);
v_discr_496_ = lean_ctor_get(v_cases_493_, 2);
v_alts_497_ = lean_ctor_get(v_cases_493_, 3);
v_isSharedCheck_536_ = !lean_is_exclusive(v_cases_493_);
if (v_isSharedCheck_536_ == 0)
{
v___x_499_ = v_cases_493_;
v_isShared_500_ = v_isSharedCheck_536_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_alts_497_);
lean_inc(v_discr_496_);
lean_inc(v_resultType_495_);
lean_inc(v_typeName_494_);
lean_dec(v_cases_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_536_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_497_);
v___x_502_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v___x_501_, v_alts_497_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_527_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_527_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_527_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_527_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v___x_507_ = lean_ptr_addr(v_alts_497_);
lean_dec_ref(v_alts_497_);
v___x_508_ = lean_ptr_addr(v_a_503_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_522_; 
v_isSharedCheck_522_ = !lean_is_exclusive(v_code_248_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_code_248_, 0);
lean_dec(v_unused_523_);
v___x_511_ = v_code_248_;
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_code_248_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 3, v_a_503_);
v___x_514_ = v___x_499_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_typeName_494_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_resultType_495_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_discr_496_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_a_503_);
v___x_514_ = v_reuseFailAlloc_521_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_514_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_516_);
v___x_518_ = v___x_505_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v_a_503_);
lean_del_object(v___x_499_);
lean_dec(v_discr_496_);
lean_dec_ref(v_resultType_495_);
lean_dec(v_typeName_494_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_code_248_);
v___x_525_ = v___x_505_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_code_248_);
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
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_del_object(v___x_499_);
lean_dec_ref(v_alts_497_);
lean_dec(v_discr_496_);
lean_dec_ref(v_resultType_495_);
lean_dec(v_typeName_494_);
lean_dec_ref_known(v_code_248_, 1);
v_a_528_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_502_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_502_);
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
default: 
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_code_248_);
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(lean_object* v_i_538_, lean_object* v_as_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_array_get_size(v_as_539_);
v___x_547_ = lean_nat_dec_lt(v_i_538_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec(v_i_538_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_as_539_);
return v___x_548_;
}
else
{
lean_object* v_a_549_; lean_object* v___y_551_; 
v_a_549_ = lean_array_fget_borrowed(v_as_539_, v_i_538_);
switch(lean_obj_tag(v_a_549_))
{
case 0:
{
lean_object* v_code_573_; 
v_code_573_ = lean_ctor_get(v_a_549_, 2);
lean_inc_ref(v_code_573_);
v___y_551_ = v_code_573_;
goto v___jp_550_;
}
case 1:
{
lean_object* v_code_574_; 
v_code_574_ = lean_ctor_get(v_a_549_, 1);
lean_inc_ref(v_code_574_);
v___y_551_ = v_code_574_;
goto v___jp_550_;
}
default: 
{
lean_object* v_code_575_; 
v_code_575_ = lean_ctor_get(v_a_549_, 0);
lean_inc_ref(v_code_575_);
v___y_551_ = v_code_575_;
goto v___jp_550_;
}
}
v___jp_550_:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v___y_551_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
lean_inc(v_a_549_);
v___x_554_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_549_, v_a_553_);
v___x_555_ = lean_ptr_addr(v_a_549_);
v___x_556_ = lean_ptr_addr(v___x_554_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_i_538_, v___x_558_);
v___x_560_ = lean_array_fset(v_as_539_, v_i_538_, v___x_554_);
lean_dec(v_i_538_);
v_i_538_ = v___x_559_;
v_as_539_ = v___x_560_;
goto _start;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v___x_554_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_i_538_, v___x_562_);
lean_dec(v_i_538_);
v_i_538_ = v___x_563_;
goto _start;
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v_as_539_);
lean_dec(v_i_538_);
v_a_565_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_552_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_552_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4___boxed(lean_object* v_i_576_, lean_object* v_as_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v_i_576_, v_as_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object* v_code_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_code_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
return v_res_592_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object* v_00_u03b2_593_, lean_object* v_m_594_, lean_object* v_a_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_594_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(v_00_u03b2_597_, v_m_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_m_598_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object* v_as_602_, size_t v_sz_603_, size_t v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_602_, v_sz_603_, v_i_604_, v_b_605_, v___y_608_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object* v_as_613_, lean_object* v_sz_614_, lean_object* v_i_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
size_t v_sz_boxed_623_; size_t v_i_boxed_624_; lean_object* v_res_625_; 
v_sz_boxed_623_ = lean_unbox_usize(v_sz_614_);
lean_dec(v_sz_614_);
v_i_boxed_624_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(v_as_613_, v_sz_boxed_623_, v_i_boxed_624_, v_b_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v_as_613_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object* v_00_u03b4_626_, lean_object* v_t_627_, lean_object* v_k_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_t_627_, v_k_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object* v_00_u03b4_630_, lean_object* v_t_631_, lean_object* v_k_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(v_00_u03b4_630_, v_t_631_, v_k_632_);
lean_dec(v_k_632_);
lean_dec(v_t_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object* v_as_634_, size_t v_sz_635_, size_t v_i_636_, lean_object* v_b_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_as_634_, v_sz_635_, v_i_636_, v_b_637_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object* v_as_645_, lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
size_t v_sz_boxed_655_; size_t v_i_boxed_656_; lean_object* v_res_657_; 
v_sz_boxed_655_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_656_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(v_as_645_, v_sz_boxed_655_, v_i_boxed_656_, v_b_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v_as_645_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(lean_object* v_00_u03b2_658_, lean_object* v_m_659_, lean_object* v_query_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_m_659_, v_query_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_662_, lean_object* v_m_663_, lean_object* v_query_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(v_00_u03b2_662_, v_m_663_, v_query_664_);
lean_dec(v_query_664_);
lean_dec_ref(v_m_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_666_, lean_object* v_m_667_, lean_object* v_query_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___redArg(v_m_667_, v_query_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_670_, lean_object* v_m_671_, lean_object* v_query_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1(v_00_u03b2_670_, v_m_671_, v_query_672_);
lean_dec(v_query_672_);
lean_dec_ref(v_m_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_674_, lean_object* v_m_675_, lean_object* v_query_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___redArg(v_m_675_, v_query_676_, v_x_677_, v_x_678_, v_x_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_682_, lean_object* v_m_683_, lean_object* v_query_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0_spec__1_spec__6(v_00_u03b2_682_, v_m_683_, v_query_684_, v_x_685_, v_x_686_, v_x_687_, v_x_688_);
lean_dec(v_query_684_);
lean_dec_ref(v_m_683_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(lean_object* v_f_690_, lean_object* v_v_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
if (lean_obj_tag(v_v_691_) == 0)
{
lean_object* v_code_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_722_; 
v_code_698_ = lean_ctor_get(v_v_691_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_v_691_);
if (v_isSharedCheck_722_ == 0)
{
v___x_700_ = v_v_691_;
v_isShared_701_ = v_isSharedCheck_722_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_code_698_);
lean_dec(v_v_691_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_722_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; 
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
v___x_702_ = lean_apply_7(v_f_690_, v_code_698_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_713_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v_a_703_);
v___x_708_ = v___x_700_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_710_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_708_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_700_);
v_a_714_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_702_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_702_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_object* v___x_723_; 
lean_dec_ref(v_f_690_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_v_691_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg___boxed(lean_object* v_f_724_, lean_object* v_v_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_724_, v_v_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(uint8_t v_pu_733_, lean_object* v_f_734_, lean_object* v_v_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_734_, v_v_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___boxed(lean_object* v_pu_743_, lean_object* v_f_744_, lean_object* v_v_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
uint8_t v_pu_boxed_752_; lean_object* v_res_753_; 
v_pu_boxed_752_ = lean_unbox(v_pu_743_);
v_res_753_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(v_pu_boxed_752_, v_f_744_, v_v_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object* v_decl_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_toSignature_761_; lean_object* v_value_762_; uint8_t v_recursive_763_; lean_object* v_inlineAttr_x3f_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_790_; 
v_toSignature_761_ = lean_ctor_get(v_decl_755_, 0);
v_value_762_ = lean_ctor_get(v_decl_755_, 1);
v_recursive_763_ = lean_ctor_get_uint8(v_decl_755_, sizeof(void*)*3);
v_inlineAttr_x3f_764_ = lean_ctor_get(v_decl_755_, 2);
v_isSharedCheck_790_ = !lean_is_exclusive(v_decl_755_);
if (v_isSharedCheck_790_ == 0)
{
v___x_766_ = v_decl_755_;
v_isShared_767_ = v_isSharedCheck_790_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_inlineAttr_x3f_764_);
lean_inc(v_value_762_);
lean_inc(v_toSignature_761_);
lean_dec(v_decl_755_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_790_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0));
v___x_769_ = lean_box(1);
v___x_770_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v___x_768_, v_value_762_, v___x_769_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_781_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_781_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_a_771_);
v___x_776_ = v___x_766_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_toSignature_761_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_771_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_inlineAttr_x3f_764_);
lean_ctor_set_uint8(v_reuseFailAlloc_780_, sizeof(void*)*3, v_recursive_763_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_776_);
v___x_778_ = v___x_773_;
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
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_del_object(v___x_766_);
lean_dec(v_inlineAttr_x3f_764_);
lean_dec_ref(v_toSignature_761_);
v_a_782_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_770_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_770_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed(lean_object* v_decl_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v_decl_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0(uint8_t v_phase_802_, lean_object* v_h_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_804_ = ((lean_object*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1));
v___x_805_ = ((lean_object*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2));
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_804_, v_phase_802_, v___x_805_, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed(lean_object* v_phase_808_, lean_object* v_h_809_){
_start:
{
uint8_t v_phase_boxed_810_; lean_object* v_res_811_; 
v_phase_boxed_810_ = lean_unbox(v_phase_808_);
v_res_811_ = l_Lean_Compiler_LCNF_reduceJpArity___lam__0(v_phase_boxed_810_, v_h_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t v_phase_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; 
v___x_813_ = lean_box(v_phase_812_);
v___f_814_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed), 2, 1);
lean_closure_set(v___f_814_, 0, v___x_813_);
v___x_815_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_816_ = 0;
v___x_817_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_815_, v_phase_812_, v___x_816_, v___f_814_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object* v_phase_818_){
_start:
{
uint8_t v_phase_boxed_819_; lean_object* v_res_820_; 
v_phase_boxed_819_ = lean_unbox(v_phase_818_);
v_res_820_ = l_Lean_Compiler_LCNF_reduceJpArity(v_phase_boxed_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_));
v___x_892_ = 1;
v___x_893_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_));
v___x_894_ = l_Lean_registerTraceClass(v___x_891_, v___x_892_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2____boxed(lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
return v_res_896_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
}
#ifdef __cplusplus
}
#endif
