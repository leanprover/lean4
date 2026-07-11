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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(lean_object* v_a_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
else
{
lean_object* v_key_74_; lean_object* v_tail_75_; uint8_t v___x_76_; 
v_key_74_ = lean_ctor_get(v_x_72_, 0);
v_tail_75_ = lean_ctor_get(v_x_72_, 2);
v___x_76_ = l_Lean_instBEqFVarId_beq(v_key_74_, v_a_71_);
if (v___x_76_ == 0)
{
v_x_72_ = v_tail_75_;
goto _start;
}
else
{
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg___boxed(lean_object* v_a_78_, lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_a_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object* v_m_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_buckets_84_; lean_object* v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v_fold_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_buckets_84_ = lean_ctor_get(v_m_82_, 1);
v___x_85_ = lean_array_get_size(v_buckets_84_);
v___x_86_ = l_Lean_instHashableFVarId_hash(v_a_83_);
v___x_87_ = 32ULL;
v___x_88_ = lean_uint64_shift_right(v___x_86_, v___x_87_);
v_fold_89_ = lean_uint64_xor(v___x_86_, v___x_88_);
v___x_90_ = 16ULL;
v___x_91_ = lean_uint64_shift_right(v_fold_89_, v___x_90_);
v___x_92_ = lean_uint64_xor(v_fold_89_, v___x_91_);
v___x_93_ = lean_uint64_to_usize(v___x_92_);
v___x_94_ = lean_usize_of_nat(v___x_85_);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_sub(v___x_94_, v___x_95_);
v___x_97_ = lean_usize_land(v___x_93_, v___x_96_);
v___x_98_ = lean_array_uget_borrowed(v_buckets_84_, v___x_97_);
v___x_99_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_83_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object* v_m_100_, lean_object* v_a_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_m_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object* v_as_104_, size_t v_sz_105_, size_t v_i_106_, lean_object* v_b_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_a_111_; uint8_t v___x_115_; 
v___x_115_ = lean_usize_dec_lt(v_i_106_, v_sz_105_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_b_107_);
return v___x_116_;
}
else
{
lean_object* v_snd_117_; lean_object* v_fst_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_160_; 
v_snd_117_ = lean_ctor_get(v_b_107_, 1);
v_fst_118_ = lean_ctor_get(v_b_107_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_b_107_);
if (v_isSharedCheck_160_ == 0)
{
v___x_120_ = v_b_107_;
v_isShared_121_ = v_isSharedCheck_160_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_117_);
lean_inc(v_fst_118_);
lean_dec(v_b_107_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_160_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_159_; 
v_fst_122_ = lean_ctor_get(v_snd_117_, 0);
v_snd_123_ = lean_ctor_get(v_snd_117_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_snd_117_);
if (v_isSharedCheck_159_ == 0)
{
v___x_125_ = v_snd_117_;
v_isShared_126_ = v_isSharedCheck_159_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snd_123_);
lean_inc(v_fst_122_);
lean_dec(v_snd_117_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_159_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v_a_127_; lean_object* v_fvarId_128_; lean_object* v_type_129_; uint8_t v___x_130_; 
v_a_127_ = lean_array_uget_borrowed(v_as_104_, v_i_106_);
v_fvarId_128_ = lean_ctor_get(v_a_127_, 0);
v_type_129_ = lean_ctor_get(v_a_127_, 2);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_fst_118_, v_fvarId_128_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; lean_object* v___x_132_; 
v___x_131_ = 0;
v___x_132_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_131_, v_a_127_, v___y_108_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec_ref_known(v___x_132_, 1);
v___x_133_ = lean_box(v___x_130_);
v___x_134_ = lean_array_push(v_fst_122_, v___x_133_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_134_);
v___x_136_ = v___x_125_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_snd_123_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_136_);
v___x_138_ = v___x_120_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_fst_118_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v_a_111_ = v___x_138_;
goto v___jp_110_;
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_del_object(v___x_125_);
lean_dec(v_snd_123_);
lean_dec(v_fst_122_);
lean_del_object(v___x_120_);
lean_dec(v_fst_118_);
v_a_141_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_132_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_132_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
lean_inc_ref(v_type_129_);
v___x_149_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(v_type_129_, v_fst_118_);
v___x_150_ = lean_box(v___x_130_);
v___x_151_ = lean_array_push(v_fst_122_, v___x_150_);
lean_inc(v_a_127_);
v___x_152_ = lean_array_push(v_snd_123_, v_a_127_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_152_);
lean_ctor_set(v___x_125_, 0, v___x_151_);
v___x_154_ = v___x_125_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_158_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_156_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_154_);
lean_ctor_set(v___x_120_, 0, v___x_149_);
v___x_156_ = v___x_120_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
v_a_111_ = v___x_156_;
goto v___jp_110_;
}
}
}
}
}
}
v___jp_110_:
{
size_t v___x_112_; size_t v___x_113_; 
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_i_106_, v___x_112_);
v_i_106_ = v___x_113_;
v_b_107_ = v_a_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object* v_as_161_, lean_object* v_sz_162_, lean_object* v_i_163_, lean_object* v_b_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
size_t v_sz_boxed_167_; size_t v_i_boxed_168_; lean_object* v_res_169_; 
v_sz_boxed_167_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_168_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_161_, v_sz_boxed_167_, v_i_boxed_168_, v_b_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v_as_161_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object* v_code_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
switch(lean_obj_tag(v_code_176_))
{
case 0:
{
lean_object* v_decl_183_; lean_object* v_k_184_; lean_object* v___x_185_; 
v_decl_183_ = lean_ctor_get(v_code_176_, 0);
v_k_184_ = lean_ctor_get(v_code_176_, 1);
lean_inc_ref(v_k_184_);
v___x_185_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_184_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_212_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_212_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_212_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_212_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
uint8_t v___y_191_; size_t v___x_207_; size_t v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_ptr_addr(v_k_184_);
v___x_208_ = lean_ptr_addr(v_a_186_);
v___x_209_ = lean_usize_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
v___y_191_ = v___x_209_;
goto v___jp_190_;
}
else
{
size_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_ptr_addr(v_decl_183_);
v___x_211_ = lean_usize_dec_eq(v___x_210_, v___x_210_);
v___y_191_ = v___x_211_;
goto v___jp_190_;
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
lean_inc_ref(v_decl_183_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; 
v_unused_202_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_203_);
v___x_193_ = v_code_176_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_dec(v_code_176_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v_a_186_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_decl_183_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_a_186_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_196_);
v___x_198_ = v___x_188_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec(v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v_code_176_);
v___x_205_ = v___x_188_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_code_176_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_176_, 2);
return v___x_185_;
}
}
case 1:
{
lean_object* v_decl_213_; lean_object* v_k_214_; lean_object* v_params_215_; lean_object* v_type_216_; lean_object* v_value_217_; lean_object* v___x_218_; 
v_decl_213_ = lean_ctor_get(v_code_176_, 0);
v_k_214_ = lean_ctor_get(v_code_176_, 1);
v_params_215_ = lean_ctor_get(v_decl_213_, 2);
v_type_216_ = lean_ctor_get(v_decl_213_, 3);
v_value_217_ = lean_ctor_get(v_decl_213_, 4);
lean_inc_ref(v_value_217_);
v___x_218_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_value_217_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; uint8_t v___x_220_; lean_object* v___x_221_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = 0;
lean_inc_ref(v_params_215_);
lean_inc_ref(v_type_216_);
lean_inc_ref(v_decl_213_);
v___x_221_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_220_, v_decl_213_, v_type_216_, v_params_215_, v_a_219_, v_a_179_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 1);
lean_inc_ref(v_k_214_);
v___x_223_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_214_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_251_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_251_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_251_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_251_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
uint8_t v___y_229_; size_t v___x_245_; size_t v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_ptr_addr(v_k_214_);
v___x_246_ = lean_ptr_addr(v_a_224_);
v___x_247_ = lean_usize_dec_eq(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
v___y_229_ = v___x_247_;
goto v___jp_228_;
}
else
{
size_t v___x_248_; size_t v___x_249_; uint8_t v___x_250_; 
v___x_248_ = lean_ptr_addr(v_decl_213_);
v___x_249_ = lean_ptr_addr(v_a_222_);
v___x_250_ = lean_usize_dec_eq(v___x_248_, v___x_249_);
v___y_229_ = v___x_250_;
goto v___jp_228_;
}
v___jp_228_:
{
if (v___y_229_ == 0)
{
lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_239_; 
v_isSharedCheck_239_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_240_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_241_);
v___x_231_ = v_code_176_;
v_isShared_232_ = v_isSharedCheck_239_;
goto v_resetjp_230_;
}
else
{
lean_dec(v_code_176_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_239_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v_a_224_);
lean_ctor_set(v___x_231_, 0, v_a_222_);
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_a_224_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_234_);
v___x_236_ = v___x_226_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v___x_243_; 
lean_dec(v_a_224_);
lean_dec(v_a_222_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v_code_176_);
v___x_243_ = v___x_226_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_code_176_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
else
{
lean_dec(v_a_222_);
lean_dec_ref_known(v_code_176_, 2);
return v___x_223_;
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref_known(v_code_176_, 2);
v_a_252_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_221_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_221_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_176_, 2);
return v___x_218_;
}
}
case 2:
{
lean_object* v_decl_260_; lean_object* v_k_261_; lean_object* v_params_262_; lean_object* v_type_263_; lean_object* v_value_264_; lean_object* v___x_265_; 
v_decl_260_ = lean_ctor_get(v_code_176_, 0);
v_k_261_ = lean_ctor_get(v_code_176_, 1);
v_params_262_ = lean_ctor_get(v_decl_260_, 2);
v_type_263_ = lean_ctor_get(v_decl_260_, 3);
v_value_264_ = lean_ctor_get(v_decl_260_, 4);
lean_inc_ref(v_value_264_);
v___x_265_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_value_264_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; size_t v_sz_273_; size_t v___x_274_; lean_object* v___x_275_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc_n(v_a_266_, 2);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_268_ = 0;
v___x_269_ = l_Lean_Compiler_LCNF_Code_collectUsed(v___x_268_, v_a_266_, v___x_267_);
lean_inc_ref(v_params_262_);
v___x_270_ = l_Array_reverse___redArg(v_params_262_);
v___x_271_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1));
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_269_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v_sz_273_ = lean_array_size(v___x_270_);
v___x_274_ = ((size_t)0ULL);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v___x_270_, v_sz_273_, v___x_274_, v___x_272_, v_a_179_);
lean_dec_ref(v___x_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_snd_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; uint8_t v___x_284_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v_snd_277_ = lean_ctor_get(v_a_276_, 1);
lean_inc(v_snd_277_);
lean_dec(v_a_276_);
v_fst_278_ = lean_ctor_get(v_snd_277_, 0);
lean_inc(v_fst_278_);
v_snd_279_ = lean_ctor_get(v_snd_277_, 1);
lean_inc(v_snd_279_);
lean_dec(v_snd_277_);
v___x_280_ = l_Array_reverse___redArg(v_snd_279_);
v___x_281_ = lean_array_get_size(v___x_280_);
v___x_282_ = lean_array_get_size(v_params_262_);
v___x_283_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
v___x_284_ = lean_bool_not(v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
lean_dec_ref(v___x_280_);
lean_dec(v_fst_278_);
lean_inc_ref(v_params_262_);
lean_inc_ref(v_type_263_);
lean_inc_ref(v_decl_260_);
v___x_285_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_268_, v_decl_260_, v_type_263_, v_params_262_, v_a_266_, v_a_179_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
lean_inc_ref(v_k_261_);
v___x_287_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_261_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_315_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_315_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_315_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_315_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
uint8_t v___y_293_; size_t v___x_309_; size_t v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_ptr_addr(v_k_261_);
v___x_310_ = lean_ptr_addr(v_a_288_);
v___x_311_ = lean_usize_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
v___y_293_ = v___x_311_;
goto v___jp_292_;
}
else
{
size_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_ptr_addr(v_decl_260_);
v___x_313_ = lean_ptr_addr(v_a_286_);
v___x_314_ = lean_usize_dec_eq(v___x_312_, v___x_313_);
v___y_293_ = v___x_314_;
goto v___jp_292_;
}
v___jp_292_:
{
if (v___y_293_ == 0)
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_304_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_305_);
v___x_295_ = v_code_176_;
v_isShared_296_ = v_isSharedCheck_303_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_code_176_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_303_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_a_288_);
lean_ctor_set(v___x_295_, 0, v_a_286_);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_286_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_a_288_);
v___x_298_ = v_reuseFailAlloc_302_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_298_);
v___x_300_ = v___x_290_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_a_288_);
lean_dec(v_a_286_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_code_176_);
v___x_307_ = v___x_290_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_code_176_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_dec(v_a_286_);
lean_dec_ref_known(v_code_176_, 2);
return v___x_287_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref_known(v_code_176_, 2);
v_a_316_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_285_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_285_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_372_; 
lean_inc_ref(v_k_261_);
lean_inc_ref(v_decl_260_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_374_);
v___x_325_ = v_code_176_;
v_isShared_326_ = v_isSharedCheck_372_;
goto v_resetjp_324_;
}
else
{
lean_dec(v_code_176_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_372_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; 
lean_inc(v_a_266_);
v___x_327_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_268_, v_a_266_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_329_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
lean_inc_ref(v___x_280_);
v___x_329_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_268_, v___x_280_, v_a_328_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_268_, v_decl_260_, v_a_330_, v___x_280_, v_a_266_, v_a_179_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_fvarId_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v_fvarId_333_ = lean_ctor_get(v_a_332_, 0);
v___x_334_ = l_Array_reverse___redArg(v_fst_278_);
lean_inc(v_a_177_);
lean_inc(v_fvarId_333_);
v___x_335_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_333_, v___x_334_, v_a_177_);
v___x_336_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_261_, v___x_335_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v___x_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_347_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_347_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_a_337_);
lean_ctor_set(v___x_325_, 0, v_a_332_);
v___x_342_ = v___x_325_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_332_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_a_337_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_342_);
v___x_344_ = v___x_339_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_dec(v_a_332_);
lean_del_object(v___x_325_);
return v___x_336_;
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_del_object(v___x_325_);
lean_dec(v_fst_278_);
lean_dec_ref(v_k_261_);
v_a_348_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_331_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_331_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_del_object(v___x_325_);
lean_dec_ref(v___x_280_);
lean_dec(v_fst_278_);
lean_dec(v_a_266_);
lean_dec_ref(v_k_261_);
lean_dec_ref(v_decl_260_);
v_a_356_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_329_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_329_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_del_object(v___x_325_);
lean_dec_ref(v___x_280_);
lean_dec(v_fst_278_);
lean_dec(v_a_266_);
lean_dec_ref(v_k_261_);
lean_dec_ref(v_decl_260_);
v_a_364_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_327_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_327_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_266_);
lean_dec_ref_known(v_code_176_, 2);
v_a_375_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_275_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_275_);
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
lean_dec_ref_known(v_code_176_, 2);
return v___x_265_;
}
}
case 3:
{
lean_object* v_fvarId_383_; lean_object* v_args_384_; lean_object* v___x_385_; 
v_fvarId_383_ = lean_ctor_get(v_code_176_, 0);
v_args_384_ = lean_ctor_get(v_code_176_, 1);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_a_177_, v_fvarId_383_);
if (lean_obj_tag(v___x_385_) == 1)
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_418_; 
lean_inc_ref(v_args_384_);
lean_inc(v_fvarId_383_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_419_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_420_);
v___x_387_ = v_code_176_;
v_isShared_388_ = v_isSharedCheck_418_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_code_176_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_418_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_val_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; size_t v_sz_395_; size_t v___x_396_; lean_object* v___x_397_; 
v_val_389_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v___x_385_, 1);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2));
v___x_392_ = lean_array_get_size(v_args_384_);
v___x_393_ = l_Array_toSubarray___redArg(v_args_384_, v___x_390_, v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_391_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v_sz_395_ = lean_array_size(v_val_389_);
v___x_396_ = ((size_t)0ULL);
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_val_389_, v_sz_395_, v___x_396_, v___x_394_);
lean_dec(v_val_389_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_409_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_fst_402_; lean_object* v___x_404_; 
v_fst_402_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_fst_402_);
lean_dec(v_a_398_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_fst_402_);
v___x_404_ = v___x_387_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_fvarId_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_fst_402_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_404_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
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
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_387_);
lean_dec(v_fvarId_383_);
v_a_410_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_397_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_397_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
else
{
lean_object* v___x_421_; 
lean_dec(v___x_385_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_code_176_);
return v___x_421_;
}
}
case 4:
{
lean_object* v_cases_422_; lean_object* v_typeName_423_; lean_object* v_resultType_424_; lean_object* v_discr_425_; lean_object* v_alts_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_465_; 
v_cases_422_ = lean_ctor_get(v_code_176_, 0);
lean_inc_ref(v_cases_422_);
v_typeName_423_ = lean_ctor_get(v_cases_422_, 0);
v_resultType_424_ = lean_ctor_get(v_cases_422_, 1);
v_discr_425_ = lean_ctor_get(v_cases_422_, 2);
v_alts_426_ = lean_ctor_get(v_cases_422_, 3);
v_isSharedCheck_465_ = !lean_is_exclusive(v_cases_422_);
if (v_isSharedCheck_465_ == 0)
{
v___x_428_ = v_cases_422_;
v_isShared_429_ = v_isSharedCheck_465_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_alts_426_);
lean_inc(v_discr_425_);
lean_inc(v_resultType_424_);
lean_inc(v_typeName_423_);
lean_dec(v_cases_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_465_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_426_);
v___x_431_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v___x_430_, v_alts_426_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_456_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_456_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
size_t v___x_436_; size_t v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_ptr_addr(v_alts_426_);
lean_dec_ref(v_alts_426_);
v___x_437_ = lean_ptr_addr(v_a_432_);
v___x_438_ = lean_usize_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_451_; 
v_isSharedCheck_451_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_452_);
v___x_440_ = v_code_176_;
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_code_176_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 3, v_a_432_);
v___x_443_ = v___x_428_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_typeName_423_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_resultType_424_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_discr_425_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_a_432_);
v___x_443_ = v_reuseFailAlloc_450_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_445_);
v___x_447_ = v___x_434_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v_a_432_);
lean_del_object(v___x_428_);
lean_dec(v_discr_425_);
lean_dec_ref(v_resultType_424_);
lean_dec(v_typeName_423_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_code_176_);
v___x_454_ = v___x_434_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_code_176_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_del_object(v___x_428_);
lean_dec_ref(v_alts_426_);
lean_dec(v_discr_425_);
lean_dec_ref(v_resultType_424_);
lean_dec(v_typeName_423_);
lean_dec_ref_known(v_code_176_, 1);
v_a_457_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_431_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_431_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
default: 
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_code_176_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(lean_object* v_i_467_, lean_object* v_as_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_array_get_size(v_as_468_);
v___x_476_ = lean_nat_dec_lt(v_i_467_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_i_467_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_as_468_);
return v___x_477_;
}
else
{
lean_object* v_a_478_; lean_object* v___y_480_; 
v_a_478_ = lean_array_fget_borrowed(v_as_468_, v_i_467_);
switch(lean_obj_tag(v_a_478_))
{
case 0:
{
lean_object* v_code_502_; 
v_code_502_ = lean_ctor_get(v_a_478_, 2);
lean_inc_ref(v_code_502_);
v___y_480_ = v_code_502_;
goto v___jp_479_;
}
case 1:
{
lean_object* v_code_503_; 
v_code_503_ = lean_ctor_get(v_a_478_, 1);
lean_inc_ref(v_code_503_);
v___y_480_ = v_code_503_;
goto v___jp_479_;
}
default: 
{
lean_object* v_code_504_; 
v_code_504_ = lean_ctor_get(v_a_478_, 0);
lean_inc_ref(v_code_504_);
v___y_480_ = v_code_504_;
goto v___jp_479_;
}
}
v___jp_479_:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v___y_480_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
lean_inc(v_a_478_);
v___x_483_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_478_, v_a_482_);
v___x_484_ = lean_ptr_addr(v_a_478_);
v___x_485_ = lean_ptr_addr(v___x_483_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_i_467_, v___x_487_);
v___x_489_ = lean_array_fset(v_as_468_, v_i_467_, v___x_483_);
lean_dec(v_i_467_);
v_i_467_ = v___x_488_;
v_as_468_ = v___x_489_;
goto _start;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___x_483_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_i_467_, v___x_491_);
lean_dec(v_i_467_);
v_i_467_ = v___x_492_;
goto _start;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v_as_468_);
lean_dec(v_i_467_);
v_a_494_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_481_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_481_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4___boxed(lean_object* v_i_505_, lean_object* v_as_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v_i_505_, v_as_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object* v_code_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_code_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
return v_res_521_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_a_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_523_, v_a_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(v_00_u03b2_526_, v_m_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_m_527_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object* v_as_531_, size_t v_sz_532_, size_t v_i_533_, lean_object* v_b_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_531_, v_sz_532_, v_i_533_, v_b_534_, v___y_537_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object* v_as_542_, lean_object* v_sz_543_, lean_object* v_i_544_, lean_object* v_b_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
size_t v_sz_boxed_552_; size_t v_i_boxed_553_; lean_object* v_res_554_; 
v_sz_boxed_552_ = lean_unbox_usize(v_sz_543_);
lean_dec(v_sz_543_);
v_i_boxed_553_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(v_as_542_, v_sz_boxed_552_, v_i_boxed_553_, v_b_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v_as_542_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object* v_00_u03b4_555_, lean_object* v_t_556_, lean_object* v_k_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_t_556_, v_k_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object* v_00_u03b4_559_, lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(v_00_u03b4_559_, v_t_560_, v_k_561_);
lean_dec(v_k_561_);
lean_dec(v_t_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object* v_as_563_, size_t v_sz_564_, size_t v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_as_563_, v_sz_564_, v_i_565_, v_b_566_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object* v_as_574_, lean_object* v_sz_575_, lean_object* v_i_576_, lean_object* v_b_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
size_t v_sz_boxed_584_; size_t v_i_boxed_585_; lean_object* v_res_586_; 
v_sz_boxed_584_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_585_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(v_as_574_, v_sz_boxed_584_, v_i_boxed_585_, v_b_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v_as_574_);
return v_res_586_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(lean_object* v_00_u03b2_587_, lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_588_, v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_591_, lean_object* v_a_592_, lean_object* v_x_593_){
_start:
{
uint8_t v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(v_00_u03b2_591_, v_a_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec(v_a_592_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(lean_object* v_f_596_, lean_object* v_v_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
if (lean_obj_tag(v_v_597_) == 0)
{
lean_object* v_code_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_628_; 
v_code_604_ = lean_ctor_get(v_v_597_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_v_597_);
if (v_isSharedCheck_628_ == 0)
{
v___x_606_ = v_v_597_;
v_isShared_607_ = v_isSharedCheck_628_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_code_604_);
lean_dec(v_v_597_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_628_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; 
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
lean_inc(v___y_598_);
v___x_608_ = lean_apply_7(v_f_596_, v_code_604_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_619_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_619_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_a_609_);
v___x_614_ = v___x_606_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_del_object(v___x_606_);
v_a_620_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_608_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_608_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
else
{
lean_object* v___x_629_; 
lean_dec_ref(v_f_596_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_v_597_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg___boxed(lean_object* v_f_630_, lean_object* v_v_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_630_, v_v_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(uint8_t v_pu_639_, lean_object* v_f_640_, lean_object* v_v_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_640_, v_v_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___boxed(lean_object* v_pu_649_, lean_object* v_f_650_, lean_object* v_v_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
uint8_t v_pu_boxed_658_; lean_object* v_res_659_; 
v_pu_boxed_658_ = lean_unbox(v_pu_649_);
v_res_659_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(v_pu_boxed_658_, v_f_650_, v_v_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object* v_decl_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_toSignature_667_; lean_object* v_value_668_; uint8_t v_recursive_669_; lean_object* v_inlineAttr_x3f_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_696_; 
v_toSignature_667_ = lean_ctor_get(v_decl_661_, 0);
v_value_668_ = lean_ctor_get(v_decl_661_, 1);
v_recursive_669_ = lean_ctor_get_uint8(v_decl_661_, sizeof(void*)*3);
v_inlineAttr_x3f_670_ = lean_ctor_get(v_decl_661_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_decl_661_);
if (v_isSharedCheck_696_ == 0)
{
v___x_672_ = v_decl_661_;
v_isShared_673_ = v_isSharedCheck_696_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_inlineAttr_x3f_670_);
lean_inc(v_value_668_);
lean_inc(v_toSignature_667_);
lean_dec(v_decl_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_696_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0));
v___x_675_ = lean_box(1);
v___x_676_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v___x_674_, v_value_668_, v___x_675_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_687_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_687_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_687_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_687_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_a_677_);
v___x_682_ = v___x_672_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_toSignature_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_677_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_inlineAttr_x3f_670_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*3, v_recursive_669_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_del_object(v___x_672_);
lean_dec(v_inlineAttr_x3f_670_);
lean_dec_ref(v_toSignature_667_);
v_a_688_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_676_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_676_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed(lean_object* v_decl_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v_decl_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0(uint8_t v_phase_708_, lean_object* v_h_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = ((lean_object*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1));
v___x_711_ = ((lean_object*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2));
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_710_, v_phase_708_, v___x_711_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed(lean_object* v_phase_714_, lean_object* v_h_715_){
_start:
{
uint8_t v_phase_boxed_716_; lean_object* v_res_717_; 
v_phase_boxed_716_ = lean_unbox(v_phase_714_);
v_res_717_ = l_Lean_Compiler_LCNF_reduceJpArity___lam__0(v_phase_boxed_716_, v_h_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t v_phase_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___f_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v___x_719_ = lean_box(v_phase_718_);
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed), 2, 1);
lean_closure_set(v___f_720_, 0, v___x_719_);
v___x_721_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_722_ = 0;
v___x_723_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_721_, v_phase_718_, v___x_722_, v___f_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object* v_phase_724_){
_start:
{
uint8_t v_phase_boxed_725_; lean_object* v_res_726_; 
v_phase_boxed_725_ = lean_unbox(v_phase_724_);
v_res_726_ = l_Lean_Compiler_LCNF_reduceJpArity(v_phase_boxed_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_));
v___x_798_ = 1;
v___x_799_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_));
v___x_800_ = l_Lean_registerTraceClass(v___x_797_, v___x_798_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2____boxed(lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
return v_res_802_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
