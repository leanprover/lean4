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
static lean_once_cell_t l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
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
lean_dec_ref(v___x_132_);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0));
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
return v___x_173_;
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
lean_dec_ref(v_code_176_);
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
lean_dec_ref(v___x_218_);
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
lean_dec_ref(v___x_221_);
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
lean_dec_ref(v_code_176_);
return v___x_223_;
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v_code_176_);
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
lean_dec_ref(v_code_176_);
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
lean_inc(v_a_266_);
lean_dec_ref(v___x_265_);
v___x_267_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_268_ = 0;
lean_inc(v_a_266_);
v___x_269_ = l_Lean_Compiler_LCNF_Code_collectUsed(v___x_268_, v_a_266_, v___x_267_);
lean_inc_ref(v_params_262_);
v___x_270_ = l_Array_reverse___redArg(v_params_262_);
v___x_271_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1, &l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1_once, _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_269_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v_sz_273_ = lean_array_size(v___x_270_);
v___x_274_ = ((size_t)0ULL);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v___x_270_, v_sz_273_, v___x_274_, v___x_272_, v_a_179_);
lean_dec_ref(v___x_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_snd_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
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
if (v___x_283_ == 0)
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_332_; 
lean_inc_ref(v_k_261_);
lean_inc_ref(v_decl_260_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_333_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_334_);
v___x_285_ = v_code_176_;
v_isShared_286_ = v_isSharedCheck_332_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_code_176_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_332_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; 
lean_inc(v_a_266_);
v___x_287_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_268_, v_a_266_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref(v___x_287_);
lean_inc_ref(v___x_280_);
v___x_289_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_268_, v___x_280_, v_a_288_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref(v___x_289_);
v___x_291_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_268_, v_decl_260_, v_a_290_, v___x_280_, v_a_266_, v_a_179_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v_fvarId_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref(v___x_291_);
v_fvarId_293_ = lean_ctor_get(v_a_292_, 0);
v___x_294_ = l_Array_reverse___redArg(v_fst_278_);
lean_inc(v_a_177_);
lean_inc(v_fvarId_293_);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_293_, v___x_294_, v_a_177_);
v___x_296_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_261_, v___x_295_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v___x_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_a_297_);
lean_ctor_set(v___x_285_, 0, v_a_292_);
v___x_302_ = v___x_285_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_292_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_a_297_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_dec(v_a_292_);
lean_del_object(v___x_285_);
return v___x_296_;
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_285_);
lean_dec(v_fst_278_);
lean_dec_ref(v_k_261_);
v_a_308_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_291_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_291_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_del_object(v___x_285_);
lean_dec_ref(v___x_280_);
lean_dec(v_fst_278_);
lean_dec(v_a_266_);
lean_dec_ref(v_k_261_);
lean_dec_ref(v_decl_260_);
v_a_316_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_289_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_289_);
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
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_del_object(v___x_285_);
lean_dec_ref(v___x_280_);
lean_dec(v_fst_278_);
lean_dec(v_a_266_);
lean_dec_ref(v_k_261_);
lean_dec_ref(v_decl_260_);
v_a_324_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_287_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_287_);
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
}
else
{
lean_object* v___x_335_; 
lean_dec_ref(v___x_280_);
lean_dec(v_fst_278_);
lean_inc_ref(v_params_262_);
lean_inc_ref(v_type_263_);
lean_inc_ref(v_decl_260_);
v___x_335_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_268_, v_decl_260_, v_type_263_, v_params_262_, v_a_266_, v_a_179_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref(v___x_335_);
lean_inc_ref(v_k_261_);
v___x_337_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_k_261_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_365_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_365_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_365_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_365_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint8_t v___y_343_; size_t v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_ptr_addr(v_k_261_);
v___x_360_ = lean_ptr_addr(v_a_338_);
v___x_361_ = lean_usize_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
v___y_343_ = v___x_361_;
goto v___jp_342_;
}
else
{
size_t v___x_362_; size_t v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_ptr_addr(v_decl_260_);
v___x_363_ = lean_ptr_addr(v_a_336_);
v___x_364_ = lean_usize_dec_eq(v___x_362_, v___x_363_);
v___y_343_ = v___x_364_;
goto v___jp_342_;
}
v___jp_342_:
{
if (v___y_343_ == 0)
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_353_; 
v_isSharedCheck_353_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; 
v_unused_354_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_355_);
v___x_345_ = v_code_176_;
v_isShared_346_ = v_isSharedCheck_353_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_code_176_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_353_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v_a_338_);
lean_ctor_set(v___x_345_, 0, v_a_336_);
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_338_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_348_);
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v___x_357_; 
lean_dec(v_a_338_);
lean_dec(v_a_336_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_code_176_);
v___x_357_ = v___x_340_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_code_176_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_dec(v_a_336_);
lean_dec_ref(v_code_176_);
return v___x_337_;
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_code_176_);
v_a_366_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_335_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_335_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_a_266_);
lean_dec_ref(v_code_176_);
v_a_374_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_275_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_275_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_dec_ref(v_code_176_);
return v___x_265_;
}
}
case 3:
{
lean_object* v_fvarId_382_; lean_object* v_args_383_; lean_object* v___x_384_; 
v_fvarId_382_ = lean_ctor_get(v_code_176_, 0);
v_args_383_ = lean_ctor_get(v_code_176_, 1);
v___x_384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_a_177_, v_fvarId_382_);
if (lean_obj_tag(v___x_384_) == 1)
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_417_; 
lean_inc_ref(v_args_383_);
lean_inc(v_fvarId_382_);
v_isSharedCheck_417_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_418_ = lean_ctor_get(v_code_176_, 1);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_419_);
v___x_386_ = v_code_176_;
v_isShared_387_ = v_isSharedCheck_417_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_code_176_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_417_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_val_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; size_t v_sz_394_; size_t v___x_395_; lean_object* v___x_396_; 
v_val_388_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_388_);
lean_dec_ref(v___x_384_);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2));
v___x_391_ = lean_array_get_size(v_args_383_);
v___x_392_ = l_Array_toSubarray___redArg(v_args_383_, v___x_389_, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_390_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v_sz_394_ = lean_array_size(v_val_388_);
v___x_395_ = ((size_t)0ULL);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_val_388_, v_sz_394_, v___x_395_, v___x_393_);
lean_dec(v_val_388_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_408_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_408_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_fst_401_; lean_object* v___x_403_; 
v_fst_401_ = lean_ctor_get(v_a_397_, 0);
lean_inc(v_fst_401_);
lean_dec(v_a_397_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_fst_401_);
v___x_403_ = v___x_386_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_fvarId_382_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_fst_401_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_403_);
v___x_405_ = v___x_399_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_del_object(v___x_386_);
lean_dec(v_fvarId_382_);
v_a_409_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_396_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_396_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
lean_object* v___x_420_; 
lean_dec(v___x_384_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_code_176_);
return v___x_420_;
}
}
case 4:
{
lean_object* v_cases_421_; lean_object* v_typeName_422_; lean_object* v_resultType_423_; lean_object* v_discr_424_; lean_object* v_alts_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_464_; 
v_cases_421_ = lean_ctor_get(v_code_176_, 0);
lean_inc_ref(v_cases_421_);
v_typeName_422_ = lean_ctor_get(v_cases_421_, 0);
v_resultType_423_ = lean_ctor_get(v_cases_421_, 1);
v_discr_424_ = lean_ctor_get(v_cases_421_, 2);
v_alts_425_ = lean_ctor_get(v_cases_421_, 3);
v_isSharedCheck_464_ = !lean_is_exclusive(v_cases_421_);
if (v_isSharedCheck_464_ == 0)
{
v___x_427_ = v_cases_421_;
v_isShared_428_ = v_isSharedCheck_464_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_alts_425_);
lean_inc(v_discr_424_);
lean_inc(v_resultType_423_);
lean_inc(v_typeName_422_);
lean_dec(v_cases_421_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_464_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_425_);
v___x_430_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v___x_429_, v_alts_425_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_455_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_455_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_455_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_455_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
size_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_ptr_addr(v_alts_425_);
lean_dec_ref(v_alts_425_);
v___x_436_ = lean_ptr_addr(v_a_431_);
v___x_437_ = lean_usize_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_450_; 
v_isSharedCheck_450_ = !lean_is_exclusive(v_code_176_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v_code_176_, 0);
lean_dec(v_unused_451_);
v___x_439_ = v_code_176_;
v_isShared_440_ = v_isSharedCheck_450_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_code_176_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_450_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 3, v_a_431_);
v___x_442_ = v___x_427_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_typeName_422_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_resultType_423_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_discr_424_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_a_431_);
v___x_442_ = v_reuseFailAlloc_449_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_444_);
v___x_446_ = v___x_433_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v_a_431_);
lean_del_object(v___x_427_);
lean_dec(v_discr_424_);
lean_dec_ref(v_resultType_423_);
lean_dec(v_typeName_422_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_code_176_);
v___x_453_ = v___x_433_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_code_176_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_427_);
lean_dec_ref(v_alts_425_);
lean_dec(v_discr_424_);
lean_dec_ref(v_resultType_423_);
lean_dec(v_typeName_422_);
lean_dec_ref(v_code_176_);
v_a_456_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_430_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_430_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
default: 
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_code_176_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(lean_object* v_i_466_, lean_object* v_as_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_array_get_size(v_as_467_);
v___x_475_ = lean_nat_dec_lt(v_i_466_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec(v_i_466_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_as_467_);
return v___x_476_;
}
else
{
lean_object* v_a_477_; lean_object* v___y_479_; 
v_a_477_ = lean_array_fget_borrowed(v_as_467_, v_i_466_);
switch(lean_obj_tag(v_a_477_))
{
case 0:
{
lean_object* v_code_501_; 
v_code_501_ = lean_ctor_get(v_a_477_, 2);
lean_inc_ref(v_code_501_);
v___y_479_ = v_code_501_;
goto v___jp_478_;
}
case 1:
{
lean_object* v_code_502_; 
v_code_502_ = lean_ctor_get(v_a_477_, 1);
lean_inc_ref(v_code_502_);
v___y_479_ = v_code_502_;
goto v___jp_478_;
}
default: 
{
lean_object* v_code_503_; 
v_code_503_ = lean_ctor_get(v_a_477_, 0);
lean_inc_ref(v_code_503_);
v___y_479_ = v_code_503_;
goto v___jp_478_;
}
}
v___jp_478_:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v___y_479_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; uint8_t v___x_485_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
lean_inc(v_a_477_);
v___x_482_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_477_, v_a_481_);
v___x_483_ = lean_ptr_addr(v_a_477_);
v___x_484_ = lean_ptr_addr(v___x_482_);
v___x_485_ = lean_usize_dec_eq(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_i_466_, v___x_486_);
v___x_488_ = lean_array_fset(v_as_467_, v_i_466_, v___x_482_);
lean_dec(v_i_466_);
v_i_466_ = v___x_487_;
v_as_467_ = v___x_488_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v___x_482_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_466_, v___x_490_);
lean_dec(v_i_466_);
v_i_466_ = v___x_491_;
goto _start;
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec_ref(v_as_467_);
lean_dec(v_i_466_);
v_a_493_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_480_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_480_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4___boxed(lean_object* v_i_504_, lean_object* v_as_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v_i_504_, v_as_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object* v_code_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(v_code_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
return v_res_520_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_a_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_522_, v_a_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object* v_00_u03b2_525_, lean_object* v_m_526_, lean_object* v_a_527_){
_start:
{
uint8_t v_res_528_; lean_object* v_r_529_; 
v_res_528_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(v_00_u03b2_525_, v_m_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_m_526_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object* v_as_530_, size_t v_sz_531_, size_t v_i_532_, lean_object* v_b_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_530_, v_sz_531_, v_i_532_, v_b_533_, v___y_536_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object* v_as_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_b_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_552_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(v_as_541_, v_sz_boxed_551_, v_i_boxed_552_, v_b_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v_as_541_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object* v_00_u03b4_554_, lean_object* v_t_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_t_555_, v_k_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object* v_00_u03b4_558_, lean_object* v_t_559_, lean_object* v_k_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(v_00_u03b4_558_, v_t_559_, v_k_560_);
lean_dec(v_k_560_);
lean_dec(v_t_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object* v_as_562_, size_t v_sz_563_, size_t v_i_564_, lean_object* v_b_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_as_562_, v_sz_563_, v_i_564_, v_b_565_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object* v_as_573_, lean_object* v_sz_574_, lean_object* v_i_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
size_t v_sz_boxed_583_; size_t v_i_boxed_584_; lean_object* v_res_585_; 
v_sz_boxed_583_ = lean_unbox_usize(v_sz_574_);
lean_dec(v_sz_574_);
v_i_boxed_584_ = lean_unbox_usize(v_i_575_);
lean_dec(v_i_575_);
v_res_585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(v_as_573_, v_sz_boxed_583_, v_i_boxed_584_, v_b_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v_as_573_);
return v_res_585_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(lean_object* v_00_u03b2_586_, lean_object* v_a_587_, lean_object* v_x_588_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_587_, v_x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_590_, lean_object* v_a_591_, lean_object* v_x_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(v_00_u03b2_590_, v_a_591_, v_x_592_);
lean_dec(v_x_592_);
lean_dec(v_a_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(lean_object* v_f_595_, lean_object* v_v_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
if (lean_obj_tag(v_v_596_) == 0)
{
lean_object* v_code_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_627_; 
v_code_603_ = lean_ctor_get(v_v_596_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_v_596_);
if (v_isSharedCheck_627_ == 0)
{
v___x_605_ = v_v_596_;
v_isShared_606_ = v_isSharedCheck_627_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_code_603_);
lean_dec(v_v_596_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_627_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; 
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
v___x_607_ = lean_apply_7(v_f_595_, v_code_603_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, lean_box(0));
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_618_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_618_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_a_608_);
v___x_613_ = v___x_605_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_613_);
v___x_615_ = v___x_610_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_del_object(v___x_605_);
v_a_619_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_607_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_607_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
else
{
lean_object* v___x_628_; 
lean_dec_ref(v_f_595_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_v_596_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg___boxed(lean_object* v_f_629_, lean_object* v_v_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_629_, v_v_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(uint8_t v_pu_638_, lean_object* v_f_639_, lean_object* v_v_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_639_, v_v_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___boxed(lean_object* v_pu_648_, lean_object* v_f_649_, lean_object* v_v_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_pu_boxed_657_; lean_object* v_res_658_; 
v_pu_boxed_657_ = lean_unbox(v_pu_648_);
v_res_658_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(v_pu_boxed_657_, v_f_649_, v_v_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object* v_decl_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_toSignature_666_; lean_object* v_value_667_; uint8_t v_recursive_668_; lean_object* v_inlineAttr_x3f_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_695_; 
v_toSignature_666_ = lean_ctor_get(v_decl_660_, 0);
v_value_667_ = lean_ctor_get(v_decl_660_, 1);
v_recursive_668_ = lean_ctor_get_uint8(v_decl_660_, sizeof(void*)*3);
v_inlineAttr_x3f_669_ = lean_ctor_get(v_decl_660_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v_decl_660_);
if (v_isSharedCheck_695_ == 0)
{
v___x_671_ = v_decl_660_;
v_isShared_672_ = v_isSharedCheck_695_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_inlineAttr_x3f_669_);
lean_inc(v_value_667_);
lean_inc(v_toSignature_666_);
lean_dec(v_decl_660_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_695_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0));
v___x_674_ = lean_box(1);
v___x_675_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v___x_673_, v_value_667_, v___x_674_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_686_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_686_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v_a_676_);
v___x_681_ = v___x_671_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_toSignature_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_inlineAttr_x3f_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*3, v_recursive_668_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_del_object(v___x_671_);
lean_dec(v_inlineAttr_x3f_669_);
lean_dec_ref(v_toSignature_666_);
v_a_687_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_675_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_675_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed(lean_object* v_decl_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v_decl_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0(uint8_t v_phase_707_, lean_object* v_h_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = ((lean_object*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1));
v___x_710_ = ((lean_object*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2));
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_709_, v_phase_707_, v___x_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed(lean_object* v_phase_713_, lean_object* v_h_714_){
_start:
{
uint8_t v_phase_boxed_715_; lean_object* v_res_716_; 
v_phase_boxed_715_ = lean_unbox(v_phase_713_);
v_res_716_ = l_Lean_Compiler_LCNF_reduceJpArity___lam__0(v_phase_boxed_715_, v_h_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t v_phase_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___f_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; 
v___x_718_ = lean_box(v_phase_717_);
v___f_719_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed), 2, 1);
lean_closure_set(v___f_719_, 0, v___x_718_);
v___x_720_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_721_ = 0;
v___x_722_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_720_, v_phase_717_, v___x_721_, v___f_719_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object* v_phase_723_){
_start:
{
uint8_t v_phase_boxed_724_; lean_object* v_res_725_; 
v_phase_boxed_724_ = lean_unbox(v_phase_723_);
v_res_725_ = l_Lean_Compiler_LCNF_reduceJpArity(v_phase_boxed_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_));
v___x_797_ = 1;
v___x_798_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_));
v___x_799_ = l_Lean_registerTraceClass(v___x_796_, v___x_797_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2____boxed(lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
return v_res_801_;
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
