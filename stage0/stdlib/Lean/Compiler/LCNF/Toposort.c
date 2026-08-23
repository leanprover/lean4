// Lean compiler output
// Module: Lean.Compiler.LCNF.Toposort
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.InitAttr
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_toposortPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toposort"};
static const lean_object* l_Lean_Compiler_LCNF_toposortPass___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toposortPass___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toposortPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toposortPass___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 7, 32, 82, 91, 245, 7, 246)}};
static const lean_object* l_Lean_Compiler_LCNF_toposortPass___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toposortPass___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toposortPass___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Compiler_LCNF_toposortPass___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_toposortPass___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toposortPass___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_toposortPass___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toposortPass___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(lean_object* v_f_1_, lean_object* v_v_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
if (lean_obj_tag(v_v_2_) == 0)
{
lean_object* v_code_10_; lean_object* v___x_11_; 
v_code_10_ = lean_ctor_get(v_v_2_, 0);
lean_inc_ref(v_code_10_);
lean_dec_ref_known(v_v_2_, 1);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_11_ = lean_apply_8(v_f_1_, v_code_10_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_11_;
}
else
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
lean_dec_ref(v_f_1_);
v_isSharedCheck_19_ = !lean_is_exclusive(v_v_2_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v_v_2_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v_v_2_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v_v_2_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_15_ = lean_box(0);
if (v_isShared_14_ == 0)
{
lean_ctor_set_tag(v___x_13_, 0);
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg___boxed(lean_object* v_f_21_, lean_object* v_v_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_21_, v_v_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_30_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(lean_object* v_a_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
else
{
lean_object* v_key_34_; lean_object* v_tail_35_; uint8_t v___x_36_; 
v_key_34_ = lean_ctor_get(v_x_32_, 0);
v_tail_35_ = lean_ctor_get(v_x_32_, 2);
v___x_36_ = lean_name_eq(v_key_34_, v_a_31_);
if (v___x_36_ == 0)
{
v_x_32_ = v_tail_35_;
goto _start;
}
else
{
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg___boxed(lean_object* v_a_38_, lean_object* v_x_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_38_, v_x_39_);
lean_dec(v_x_39_);
lean_dec(v_a_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
return v_x_42_;
}
else
{
lean_object* v_key_44_; lean_object* v_value_45_; lean_object* v_tail_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_72_; 
v_key_44_ = lean_ctor_get(v_x_43_, 0);
v_value_45_ = lean_ctor_get(v_x_43_, 1);
v_tail_46_ = lean_ctor_get(v_x_43_, 2);
v_isSharedCheck_72_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_72_ == 0)
{
v___x_48_ = v_x_43_;
v_isShared_49_ = v_isSharedCheck_72_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_tail_46_);
lean_inc(v_value_45_);
lean_inc(v_key_44_);
lean_dec(v_x_43_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_72_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; uint64_t v___y_52_; 
v___x_50_ = lean_array_get_size(v_x_42_);
if (lean_obj_tag(v_key_44_) == 0)
{
uint64_t v___x_70_; 
v___x_70_ = 1723ULL;
v___y_52_ = v___x_70_;
goto v___jp_51_;
}
else
{
uint64_t v_hash_71_; 
v_hash_71_ = lean_ctor_get_uint64(v_key_44_, sizeof(void*)*2);
v___y_52_ = v_hash_71_;
goto v___jp_51_;
}
v___jp_51_:
{
uint64_t v___x_53_; uint64_t v___x_54_; uint64_t v_fold_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_53_ = 32ULL;
v___x_54_ = lean_uint64_shift_right(v___y_52_, v___x_53_);
v_fold_55_ = lean_uint64_xor(v___y_52_, v___x_54_);
v___x_56_ = 16ULL;
v___x_57_ = lean_uint64_shift_right(v_fold_55_, v___x_56_);
v___x_58_ = lean_uint64_xor(v_fold_55_, v___x_57_);
v___x_59_ = lean_uint64_to_usize(v___x_58_);
v___x_60_ = lean_usize_of_nat(v___x_50_);
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_sub(v___x_60_, v___x_61_);
v___x_63_ = lean_usize_land(v___x_59_, v___x_62_);
v___x_64_ = lean_array_uget_borrowed(v_x_42_, v___x_63_);
lean_inc(v___x_64_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 2, v___x_64_);
v___x_66_ = v___x_48_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_key_44_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_value_45_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v___x_64_);
v___x_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_array_uset(v_x_42_, v___x_63_, v___x_66_);
v_x_42_ = v___x_67_;
v_x_43_ = v_tail_46_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(lean_object* v_i_73_, lean_object* v_source_74_, lean_object* v_target_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_array_get_size(v_source_74_);
v___x_77_ = lean_nat_dec_lt(v_i_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec_ref(v_source_74_);
lean_dec(v_i_73_);
return v_target_75_;
}
else
{
lean_object* v_es_78_; lean_object* v___x_79_; lean_object* v_source_80_; lean_object* v_target_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_es_78_ = lean_array_fget(v_source_74_, v_i_73_);
v___x_79_ = lean_box(0);
v_source_80_ = lean_array_fset(v_source_74_, v_i_73_, v___x_79_);
v_target_81_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_target_75_, v_es_78_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_i_73_, v___x_82_);
lean_dec(v_i_73_);
v_i_73_ = v___x_83_;
v_source_74_ = v_source_80_;
v_target_75_ = v_target_81_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(lean_object* v_data_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_nbuckets_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_86_ = lean_array_get_size(v_data_85_);
v___x_87_ = lean_unsigned_to_nat(2u);
v_nbuckets_88_ = lean_nat_mul(v___x_86_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_box(0);
v___x_91_ = lean_mk_array(v_nbuckets_88_, v___x_90_);
v___x_92_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v___x_89_, v_data_85_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object* v_m_93_, lean_object* v_a_94_, lean_object* v_b_95_){
_start:
{
lean_object* v_size_96_; lean_object* v_buckets_97_; lean_object* v___x_98_; uint64_t v___y_100_; 
v_size_96_ = lean_ctor_get(v_m_93_, 0);
v_buckets_97_ = lean_ctor_get(v_m_93_, 1);
v___x_98_ = lean_array_get_size(v_buckets_97_);
if (lean_obj_tag(v_a_94_) == 0)
{
uint64_t v___x_137_; 
v___x_137_ = 1723ULL;
v___y_100_ = v___x_137_;
goto v___jp_99_;
}
else
{
uint64_t v_hash_138_; 
v_hash_138_ = lean_ctor_get_uint64(v_a_94_, sizeof(void*)*2);
v___y_100_ = v_hash_138_;
goto v___jp_99_;
}
v___jp_99_:
{
uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v_fold_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v_bkt_112_; uint8_t v___x_113_; 
v___x_101_ = 32ULL;
v___x_102_ = lean_uint64_shift_right(v___y_100_, v___x_101_);
v_fold_103_ = lean_uint64_xor(v___y_100_, v___x_102_);
v___x_104_ = 16ULL;
v___x_105_ = lean_uint64_shift_right(v_fold_103_, v___x_104_);
v___x_106_ = lean_uint64_xor(v_fold_103_, v___x_105_);
v___x_107_ = lean_uint64_to_usize(v___x_106_);
v___x_108_ = lean_usize_of_nat(v___x_98_);
v___x_109_ = ((size_t)1ULL);
v___x_110_ = lean_usize_sub(v___x_108_, v___x_109_);
v___x_111_ = lean_usize_land(v___x_107_, v___x_110_);
v_bkt_112_ = lean_array_uget_borrowed(v_buckets_97_, v___x_111_);
v___x_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_94_, v_bkt_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_134_; 
lean_inc_ref(v_buckets_97_);
lean_inc(v_size_96_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_m_93_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_m_93_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_m_93_, 0);
lean_dec(v_unused_136_);
v___x_115_ = v_m_93_;
v_isShared_116_ = v_isSharedCheck_134_;
goto v_resetjp_114_;
}
else
{
lean_dec(v_m_93_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_134_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v_size_x27_118_; lean_object* v___x_119_; lean_object* v_buckets_x27_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v_size_x27_118_ = lean_nat_add(v_size_96_, v___x_117_);
lean_dec(v_size_96_);
lean_inc(v_bkt_112_);
v___x_119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_119_, 0, v_a_94_);
lean_ctor_set(v___x_119_, 1, v_b_95_);
lean_ctor_set(v___x_119_, 2, v_bkt_112_);
v_buckets_x27_120_ = lean_array_uset(v_buckets_97_, v___x_111_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(4u);
v___x_122_ = lean_nat_mul(v_size_x27_118_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(3u);
v___x_124_ = lean_nat_div(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_array_get_size(v_buckets_x27_120_);
v___x_126_ = lean_nat_dec_le(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v_val_127_; lean_object* v___x_129_; 
v_val_127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_120_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_val_127_);
lean_ctor_set(v___x_115_, 0, v_size_x27_118_);
v___x_129_ = v___x_115_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_size_x27_118_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_val_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v___x_132_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_buckets_x27_120_);
lean_ctor_set(v___x_115_, 0, v_size_x27_118_);
v___x_132_ = v___x_115_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_118_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_buckets_x27_120_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_dec(v_b_95_);
lean_dec(v_a_94_);
return v_m_93_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object* v_m_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_buckets_141_; lean_object* v___x_142_; uint64_t v___y_144_; 
v_buckets_141_ = lean_ctor_get(v_m_139_, 1);
v___x_142_ = lean_array_get_size(v_buckets_141_);
if (lean_obj_tag(v_a_140_) == 0)
{
uint64_t v___x_158_; 
v___x_158_ = 1723ULL;
v___y_144_ = v___x_158_;
goto v___jp_143_;
}
else
{
uint64_t v_hash_159_; 
v_hash_159_ = lean_ctor_get_uint64(v_a_140_, sizeof(void*)*2);
v___y_144_ = v_hash_159_;
goto v___jp_143_;
}
v___jp_143_:
{
uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v_fold_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_145_ = 32ULL;
v___x_146_ = lean_uint64_shift_right(v___y_144_, v___x_145_);
v_fold_147_ = lean_uint64_xor(v___y_144_, v___x_146_);
v___x_148_ = 16ULL;
v___x_149_ = lean_uint64_shift_right(v_fold_147_, v___x_148_);
v___x_150_ = lean_uint64_xor(v_fold_147_, v___x_149_);
v___x_151_ = lean_uint64_to_usize(v___x_150_);
v___x_152_ = lean_usize_of_nat(v___x_142_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_sub(v___x_152_, v___x_153_);
v___x_155_ = lean_usize_land(v___x_151_, v___x_154_);
v___x_156_ = lean_array_uget_borrowed(v_buckets_141_, v___x_155_);
v___x_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_140_, v___x_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object* v_m_160_, lean_object* v_a_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_m_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_key_167_; lean_object* v_value_168_; lean_object* v_tail_169_; uint8_t v___x_170_; 
v_key_167_ = lean_ctor_get(v_x_165_, 0);
v_value_168_ = lean_ctor_get(v_x_165_, 1);
v_tail_169_ = lean_ctor_get(v_x_165_, 2);
v___x_170_ = lean_name_eq(v_key_167_, v_a_164_);
if (v___x_170_ == 0)
{
v_x_165_ = v_tail_169_;
goto _start;
}
else
{
lean_object* v___x_172_; 
lean_inc(v_value_168_);
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v_value_168_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg___boxed(lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_173_, v_x_174_);
lean_dec(v_x_174_);
lean_dec(v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(lean_object* v_m_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_buckets_178_; lean_object* v___x_179_; uint64_t v___y_181_; 
v_buckets_178_ = lean_ctor_get(v_m_176_, 1);
v___x_179_ = lean_array_get_size(v_buckets_178_);
if (lean_obj_tag(v_a_177_) == 0)
{
uint64_t v___x_195_; 
v___x_195_ = 1723ULL;
v___y_181_ = v___x_195_;
goto v___jp_180_;
}
else
{
uint64_t v_hash_196_; 
v_hash_196_ = lean_ctor_get_uint64(v_a_177_, sizeof(void*)*2);
v___y_181_ = v_hash_196_;
goto v___jp_180_;
}
v___jp_180_:
{
uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v_fold_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_182_ = 32ULL;
v___x_183_ = lean_uint64_shift_right(v___y_181_, v___x_182_);
v_fold_184_ = lean_uint64_xor(v___y_181_, v___x_183_);
v___x_185_ = 16ULL;
v___x_186_ = lean_uint64_shift_right(v_fold_184_, v___x_185_);
v___x_187_ = lean_uint64_xor(v_fold_184_, v___x_186_);
v___x_188_ = lean_uint64_to_usize(v___x_187_);
v___x_189_ = lean_usize_of_nat(v___x_179_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_sub(v___x_189_, v___x_190_);
v___x_192_ = lean_usize_land(v___x_188_, v___x_191_);
v___x_193_ = lean_array_uget_borrowed(v_buckets_178_, v___x_192_);
v___x_194_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_177_, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg___boxed(lean_object* v_m_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_m_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(lean_object* v_pu_200_, lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
uint8_t v_pu_boxed_209_; lean_object* v_res_210_; 
v_pu_boxed_209_ = lean_unbox(v_pu_200_);
v_res_210_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(v_pu_boxed_209_, v_x_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec_ref(v_x_201_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(uint8_t v_pu_211_, lean_object* v_decl_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___y_221_; lean_object* v___x_236_; lean_object* v_toSignature_237_; lean_object* v_seen_238_; lean_object* v_value_239_; lean_object* v_name_240_; uint8_t v___x_241_; 
v___x_236_ = lean_st_ref_get(v_a_214_);
v_toSignature_237_ = lean_ctor_get(v_decl_212_, 0);
v_seen_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_seen_238_);
lean_dec(v___x_236_);
v_value_239_ = lean_ctor_get(v_decl_212_, 1);
v_name_240_ = lean_ctor_get(v_toSignature_237_, 0);
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_seen_238_, v_name_240_);
lean_dec_ref(v_seen_238_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_seen_244_; lean_object* v_order_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_265_; 
v___x_242_ = lean_st_ref_get(v_a_218_);
v___x_243_ = lean_st_ref_take(v_a_214_);
v_seen_244_ = lean_ctor_get(v___x_243_, 0);
v_order_245_ = lean_ctor_get(v___x_243_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_265_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_order_245_);
lean_inc(v_seen_244_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_box(0);
lean_inc(v_name_240_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_seen_244_, v_name_240_, v___x_249_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_250_);
v___x_252_ = v___x_247_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_order_245_);
v___x_252_ = v_reuseFailAlloc_264_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___f_255_; lean_object* v___x_256_; 
v___x_253_ = lean_st_ref_put(v_a_214_, v___x_252_);
v___x_254_ = lean_box(v_pu_211_);
v___f_255_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed), 9, 1);
lean_closure_set(v___f_255_, 0, v___x_254_);
lean_inc_ref(v_value_239_);
v___x_256_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___f_255_, v_value_239_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___y_258_; lean_object* v_env_261_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_256_, 1);
v_env_261_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref_n(v_env_261_, 2);
lean_dec(v___x_242_);
lean_inc(v_name_240_);
v___x_262_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_261_, v_name_240_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; 
lean_inc(v_name_240_);
v___x_263_ = lean_get_init_fn_name_for(v_env_261_, v_name_240_);
v___y_258_ = v___x_263_;
goto v___jp_257_;
}
else
{
lean_dec_ref(v_env_261_);
v___y_258_ = v___x_262_;
goto v___jp_257_;
}
v___jp_257_:
{
if (lean_obj_tag(v___y_258_) == 1)
{
lean_object* v_val_259_; lean_object* v___x_260_; 
v_val_259_ = lean_ctor_get(v___y_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v___y_258_, 1);
v___x_260_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_211_, v_val_259_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_val_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_dec_ref_known(v___x_260_, 1);
v___y_221_ = v_a_214_;
goto v___jp_220_;
}
else
{
lean_dec_ref(v_decl_212_);
return v___x_260_;
}
}
else
{
lean_dec(v___y_258_);
v___y_221_ = v_a_214_;
goto v___jp_220_;
}
}
}
else
{
lean_dec(v___x_242_);
lean_dec_ref(v_decl_212_);
return v___x_256_;
}
}
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec_ref(v_decl_212_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v_seen_223_; lean_object* v_order_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_235_; 
v___x_222_ = lean_st_ref_take(v___y_221_);
v_seen_223_ = lean_ctor_get(v___x_222_, 0);
v_order_224_ = lean_ctor_get(v___x_222_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_235_ == 0)
{
v___x_226_ = v___x_222_;
v_isShared_227_ = v_isSharedCheck_235_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_order_224_);
lean_inc(v_seen_223_);
lean_dec(v___x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_235_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_array_push(v_order_224_, v_decl_212_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_seen_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_st_ref_put(v___y_221_, v___x_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(uint8_t v_pu_268_, lean_object* v_declName_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_a_270_, v_declName_269_);
if (lean_obj_tag(v___x_277_) == 1)
{
lean_object* v_val_278_; lean_object* v___x_279_; 
v_val_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_277_, 1);
v___x_279_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_268_, v_val_278_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(uint8_t v_pu_282_, lean_object* v_code_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
if (lean_obj_tag(v_code_283_) == 0)
{
lean_object* v_decl_291_; lean_object* v_value_292_; 
v_decl_291_ = lean_ctor_get(v_code_283_, 0);
v_value_292_ = lean_ctor_get(v_decl_291_, 3);
switch(lean_obj_tag(v_value_292_))
{
case 3:
{
lean_object* v_declName_293_; lean_object* v___x_294_; 
v_declName_293_ = lean_ctor_get(v_value_292_, 0);
v___x_294_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_282_, v_declName_293_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
return v___x_294_;
}
case 9:
{
lean_object* v_fn_295_; lean_object* v___x_296_; 
v_fn_295_ = lean_ctor_get(v_value_292_, 0);
v___x_296_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_282_, v_fn_295_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
return v___x_296_;
}
case 10:
{
lean_object* v_fn_297_; lean_object* v___x_298_; 
v_fn_297_ = lean_ctor_get(v_value_292_, 0);
v___x_298_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_282_, v_fn_297_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
return v___x_298_;
}
default: 
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(uint8_t v_pu_303_, uint8_t v_pu_304_, lean_object* v_as_305_, size_t v_i_306_, size_t v_stop_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___y_317_; uint8_t v___x_322_; 
v___x_322_ = lean_usize_dec_eq(v_i_306_, v_stop_307_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_array_uget_borrowed(v_as_305_, v_i_306_);
switch(lean_obj_tag(v___x_323_))
{
case 0:
{
lean_object* v_code_324_; lean_object* v___x_325_; 
v_code_324_ = lean_ctor_get(v___x_323_, 2);
v___x_325_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_303_, v_pu_304_, v_code_324_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v___y_317_ = v___x_325_;
goto v___jp_316_;
}
case 1:
{
lean_object* v_code_326_; lean_object* v___x_327_; 
v_code_326_ = lean_ctor_get(v___x_323_, 1);
v___x_327_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_303_, v_pu_304_, v_code_326_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v___y_317_ = v___x_327_;
goto v___jp_316_;
}
default: 
{
lean_object* v_code_328_; lean_object* v___x_329_; 
v_code_328_ = lean_ctor_get(v___x_323_, 0);
v___x_329_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_303_, v_pu_304_, v_code_328_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v___y_317_ = v___x_329_;
goto v___jp_316_;
}
}
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_308_);
return v___x_330_;
}
v___jp_316_:
{
if (lean_obj_tag(v___y_317_) == 0)
{
lean_object* v_a_318_; size_t v___x_319_; size_t v___x_320_; 
v_a_318_ = lean_ctor_get(v___y_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___y_317_, 1);
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_add(v_i_306_, v___x_319_);
v_i_306_ = v___x_320_;
v_b_308_ = v_a_318_;
goto _start;
}
else
{
return v___y_317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(uint8_t v_pu_331_, uint8_t v_pu_332_, lean_object* v_c_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_331_, v_c_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_387_; 
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_341_, 0);
lean_dec(v_unused_388_);
v___x_343_ = v___x_341_;
v_isShared_344_ = v_isSharedCheck_387_;
goto v_resetjp_342_;
}
else
{
lean_dec(v___x_341_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_387_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
switch(lean_obj_tag(v_c_333_))
{
case 0:
{
lean_object* v_k_345_; 
lean_del_object(v___x_343_);
v_k_345_ = lean_ctor_get(v_c_333_, 1);
v_c_333_ = v_k_345_;
goto _start;
}
case 1:
{
lean_object* v_decl_347_; lean_object* v_k_348_; lean_object* v_value_349_; lean_object* v___x_350_; 
lean_del_object(v___x_343_);
v_decl_347_ = lean_ctor_get(v_c_333_, 0);
v_k_348_ = lean_ctor_get(v_c_333_, 1);
v_value_349_ = lean_ctor_get(v_decl_347_, 4);
v___x_350_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_331_, v_pu_332_, v_value_349_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_dec_ref_known(v___x_350_, 1);
v_c_333_ = v_k_348_;
goto _start;
}
else
{
return v___x_350_;
}
}
case 2:
{
lean_object* v_decl_352_; lean_object* v_k_353_; lean_object* v_value_354_; lean_object* v___x_355_; 
lean_del_object(v___x_343_);
v_decl_352_ = lean_ctor_get(v_c_333_, 0);
v_k_353_ = lean_ctor_get(v_c_333_, 1);
v_value_354_ = lean_ctor_get(v_decl_352_, 4);
v___x_355_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_331_, v_pu_332_, v_value_354_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_dec_ref_known(v___x_355_, 1);
v_c_333_ = v_k_353_;
goto _start;
}
else
{
return v___x_355_;
}
}
case 4:
{
lean_object* v_cases_357_; lean_object* v_alts_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_cases_357_ = lean_ctor_get(v_c_333_, 0);
v_alts_358_ = lean_ctor_get(v_cases_357_, 3);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v_alts_358_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v___x_364_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_361_);
v___x_364_ = v___x_343_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_361_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
lean_del_object(v___x_343_);
v___x_366_ = ((size_t)0ULL);
v___x_367_ = lean_usize_of_nat(v___x_360_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_331_, v_pu_332_, v_alts_358_, v___x_366_, v___x_367_, v___x_361_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_368_;
}
}
case 7:
{
lean_object* v_k_369_; 
lean_del_object(v___x_343_);
v_k_369_ = lean_ctor_get(v_c_333_, 3);
v_c_333_ = v_k_369_;
goto _start;
}
case 8:
{
lean_object* v_k_371_; 
lean_del_object(v___x_343_);
v_k_371_ = lean_ctor_get(v_c_333_, 3);
v_c_333_ = v_k_371_;
goto _start;
}
case 9:
{
lean_object* v_k_373_; 
lean_del_object(v___x_343_);
v_k_373_ = lean_ctor_get(v_c_333_, 5);
v_c_333_ = v_k_373_;
goto _start;
}
case 10:
{
lean_object* v_k_375_; 
lean_del_object(v___x_343_);
v_k_375_ = lean_ctor_get(v_c_333_, 2);
v_c_333_ = v_k_375_;
goto _start;
}
case 11:
{
lean_object* v_k_377_; 
lean_del_object(v___x_343_);
v_k_377_ = lean_ctor_get(v_c_333_, 2);
v_c_333_ = v_k_377_;
goto _start;
}
case 12:
{
lean_object* v_k_379_; 
lean_del_object(v___x_343_);
v_k_379_ = lean_ctor_get(v_c_333_, 3);
v_c_333_ = v_k_379_;
goto _start;
}
case 13:
{
lean_object* v_k_381_; 
lean_del_object(v___x_343_);
v_k_381_ = lean_ctor_get(v_c_333_, 1);
v_c_333_ = v_k_381_;
goto _start;
}
default: 
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_box(0);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_383_);
v___x_385_ = v___x_343_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
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
}
else
{
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t v_pu_389_, lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_389_, v_pu_389_, v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object* v_pu_399_, lean_object* v_declName_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
uint8_t v_pu_boxed_408_; lean_object* v_res_409_; 
v_pu_boxed_408_ = lean_unbox(v_pu_399_);
v_res_409_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_boxed_408_, v_declName_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_declName_400_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object* v_pu_410_, lean_object* v_code_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
uint8_t v_pu_boxed_419_; lean_object* v_res_420_; 
v_pu_boxed_419_ = lean_unbox(v_pu_410_);
v_res_420_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_boxed_419_, v_code_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec_ref(v_code_411_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object* v_pu_421_, lean_object* v_pu_422_, lean_object* v_as_423_, lean_object* v_i_424_, lean_object* v_stop_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v_pu_boxed_434_; uint8_t v_pu_boxed_435_; size_t v_i_boxed_436_; size_t v_stop_boxed_437_; lean_object* v_res_438_; 
v_pu_boxed_434_ = lean_unbox(v_pu_421_);
v_pu_boxed_435_ = lean_unbox(v_pu_422_);
v_i_boxed_436_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_stop_boxed_437_ = lean_unbox_usize(v_stop_425_);
lean_dec(v_stop_425_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_434_, v_pu_boxed_435_, v_as_423_, v_i_boxed_436_, v_stop_boxed_437_, v_b_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec_ref(v_as_423_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object* v_pu_439_, lean_object* v_pu_440_, lean_object* v_c_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
uint8_t v_pu_boxed_449_; uint8_t v_pu_boxed_450_; lean_object* v_res_451_; 
v_pu_boxed_449_ = lean_unbox(v_pu_439_);
v_pu_boxed_450_ = lean_unbox(v_pu_440_);
v_res_451_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_449_, v_pu_boxed_450_, v_c_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec_ref(v_c_441_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object* v_pu_452_, lean_object* v_decl_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_pu_boxed_461_; lean_object* v_res_462_; 
v_pu_boxed_461_ = lean_unbox(v_pu_452_);
v_res_462_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_boxed_461_, v_decl_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(uint8_t v_pu_463_, lean_object* v_f_464_, lean_object* v_v_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_464_, v_v_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object* v_pu_474_, lean_object* v_f_475_, lean_object* v_v_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v_pu_boxed_484_; lean_object* v_res_485_; 
v_pu_boxed_484_ = lean_unbox(v_pu_474_);
v_res_485_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_boxed_484_, v_f_475_, v_v_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_485_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object* v_00_u03b2_486_, lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_487_, v_a_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object* v_00_u03b2_490_, lean_object* v_m_491_, lean_object* v_a_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_490_, v_m_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_m_491_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(lean_object* v_00_u03b2_495_, lean_object* v_m_496_, lean_object* v_a_497_, lean_object* v_b_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_m_496_, v_a_497_, v_b_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_501_, v_a_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(lean_object* v_00_u03b2_504_, lean_object* v_m_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(v_00_u03b2_504_, v_m_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_m_505_);
return v_res_507_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object* v_00_u03b2_508_, lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_509_, v_x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object* v_00_u03b2_512_, lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_512_, v_a_513_, v_x_514_);
lean_dec(v_x_514_);
lean_dec(v_a_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(lean_object* v_00_u03b2_517_, lean_object* v_data_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_data_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(lean_object* v_00_u03b2_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(v_00_u03b2_524_, v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_528_, lean_object* v_i_529_, lean_object* v_source_530_, lean_object* v_target_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v_i_529_, v_source_530_, v_target_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_x_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t v_pu_537_, lean_object* v_as_538_, size_t v_i_539_, size_t v_stop_540_, lean_object* v_b_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
lean_inc(v___x_550_);
v___x_551_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_537_, v___x_550_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; size_t v___x_553_; size_t v___x_554_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_539_, v___x_553_);
v_i_539_ = v___x_554_;
v_b_541_ = v_a_552_;
goto _start;
}
else
{
return v___x_551_;
}
}
else
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v_b_541_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object* v_pu_557_, lean_object* v_as_558_, lean_object* v_i_559_, lean_object* v_stop_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v_pu_boxed_569_; size_t v_i_boxed_570_; size_t v_stop_boxed_571_; lean_object* v_res_572_; 
v_pu_boxed_569_ = lean_unbox(v_pu_557_);
v_i_boxed_570_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_stop_boxed_571_ = lean_unbox_usize(v_stop_560_);
lean_dec(v_stop_560_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_569_, v_as_558_, v_i_boxed_570_, v_stop_boxed_571_, v_b_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_as_558_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t v_pu_573_, lean_object* v_decls_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_array_get_size(v_decls_574_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_nat_dec_lt(v___x_582_, v___x_583_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
return v___x_586_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = lean_nat_dec_le(v___x_583_, v___x_583_);
if (v___x_587_ == 0)
{
if (v___x_585_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_584_);
return v___x_588_;
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_583_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_573_, v_decls_574_, v___x_589_, v___x_590_, v___x_584_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_591_;
}
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((size_t)0ULL);
v___x_593_ = lean_usize_of_nat(v___x_583_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_573_, v_decls_574_, v___x_592_, v___x_593_, v___x_584_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object* v_pu_595_, lean_object* v_decls_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
uint8_t v_pu_boxed_604_; lean_object* v_res_605_; 
v_pu_boxed_604_ = lean_unbox(v_pu_595_);
v_res_605_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_boxed_604_, v_decls_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v_decls_596_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t v_sz_606_, size_t v_i_607_, lean_object* v_bs_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_607_, v_sz_606_);
if (v___x_609_ == 0)
{
return v_bs_608_;
}
else
{
lean_object* v_v_610_; lean_object* v_toSignature_611_; lean_object* v_name_612_; lean_object* v___x_613_; lean_object* v_bs_x27_614_; lean_object* v___x_615_; size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v_v_610_ = lean_array_uget(v_bs_608_, v_i_607_);
v_toSignature_611_ = lean_ctor_get(v_v_610_, 0);
v_name_612_ = lean_ctor_get(v_toSignature_611_, 0);
lean_inc(v_name_612_);
v___x_613_ = lean_unsigned_to_nat(0u);
v_bs_x27_614_ = lean_array_uset(v_bs_608_, v_i_607_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_name_612_);
lean_ctor_set(v___x_615_, 1, v_v_610_);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_607_, v___x_616_);
v___x_618_ = lean_array_uset(v_bs_x27_614_, v_i_607_, v___x_615_);
v_i_607_ = v___x_617_;
v_bs_608_ = v___x_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object* v_sz_620_, lean_object* v_i_621_, lean_object* v_bs_622_){
_start:
{
size_t v_sz_boxed_623_; size_t v_i_boxed_624_; lean_object* v_res_625_; 
v_sz_boxed_623_ = lean_unbox_usize(v_sz_620_);
lean_dec(v_sz_620_);
v_i_boxed_624_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_623_, v_i_boxed_624_, v_bs_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_dec(v_b_627_);
lean_dec(v_a_626_);
return v_x_628_;
}
else
{
lean_object* v_key_629_; lean_object* v_value_630_; lean_object* v_tail_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_643_; 
v_key_629_ = lean_ctor_get(v_x_628_, 0);
v_value_630_ = lean_ctor_get(v_x_628_, 1);
v_tail_631_ = lean_ctor_get(v_x_628_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_643_ == 0)
{
v___x_633_ = v_x_628_;
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_tail_631_);
lean_inc(v_value_630_);
lean_inc(v_key_629_);
lean_dec(v_x_628_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
uint8_t v___x_635_; 
v___x_635_ = lean_name_eq(v_key_629_, v_a_626_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_626_, v_b_627_, v_tail_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 2, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_key_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_value_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v___x_641_; 
lean_dec(v_value_630_);
lean_dec(v_key_629_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_b_627_);
lean_ctor_set(v___x_633_, 0, v_a_626_);
v___x_641_ = v___x_633_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_626_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_b_627_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_tail_631_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(lean_object* v_m_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_size_647_; lean_object* v_buckets_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_694_; 
v_size_647_ = lean_ctor_get(v_m_644_, 0);
v_buckets_648_ = lean_ctor_get(v_m_644_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_m_644_);
if (v_isSharedCheck_694_ == 0)
{
v___x_650_ = v_m_644_;
v_isShared_651_ = v_isSharedCheck_694_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_buckets_648_);
lean_inc(v_size_647_);
lean_dec(v_m_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_694_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; uint64_t v___y_654_; 
v___x_652_ = lean_array_get_size(v_buckets_648_);
if (lean_obj_tag(v_a_645_) == 0)
{
uint64_t v___x_692_; 
v___x_692_ = 1723ULL;
v___y_654_ = v___x_692_;
goto v___jp_653_;
}
else
{
uint64_t v_hash_693_; 
v_hash_693_ = lean_ctor_get_uint64(v_a_645_, sizeof(void*)*2);
v___y_654_ = v_hash_693_;
goto v___jp_653_;
}
v___jp_653_:
{
uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v_fold_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v_bkt_666_; uint8_t v___x_667_; 
v___x_655_ = 32ULL;
v___x_656_ = lean_uint64_shift_right(v___y_654_, v___x_655_);
v_fold_657_ = lean_uint64_xor(v___y_654_, v___x_656_);
v___x_658_ = 16ULL;
v___x_659_ = lean_uint64_shift_right(v_fold_657_, v___x_658_);
v___x_660_ = lean_uint64_xor(v_fold_657_, v___x_659_);
v___x_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = lean_usize_of_nat(v___x_652_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_sub(v___x_662_, v___x_663_);
v___x_665_ = lean_usize_land(v___x_661_, v___x_664_);
v_bkt_666_ = lean_array_uget_borrowed(v_buckets_648_, v___x_665_);
v___x_667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_645_, v_bkt_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v_size_x27_669_; lean_object* v___x_670_; lean_object* v_buckets_x27_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_668_ = lean_unsigned_to_nat(1u);
v_size_x27_669_ = lean_nat_add(v_size_647_, v___x_668_);
lean_dec(v_size_647_);
lean_inc(v_bkt_666_);
v___x_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_670_, 0, v_a_645_);
lean_ctor_set(v___x_670_, 1, v_b_646_);
lean_ctor_set(v___x_670_, 2, v_bkt_666_);
v_buckets_x27_671_ = lean_array_uset(v_buckets_648_, v___x_665_, v___x_670_);
v___x_672_ = lean_unsigned_to_nat(4u);
v___x_673_ = lean_nat_mul(v_size_x27_669_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(3u);
v___x_675_ = lean_nat_div(v___x_673_, v___x_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_array_get_size(v_buckets_x27_671_);
v___x_677_ = lean_nat_dec_le(v___x_675_, v___x_676_);
lean_dec(v___x_675_);
if (v___x_677_ == 0)
{
lean_object* v_val_678_; lean_object* v___x_680_; 
v_val_678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_671_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_val_678_);
lean_ctor_set(v___x_650_, 0, v_size_x27_669_);
v___x_680_ = v___x_650_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_size_x27_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_val_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v___x_683_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_buckets_x27_671_);
lean_ctor_set(v___x_650_, 0, v_size_x27_669_);
v___x_683_ = v___x_650_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_size_x27_669_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_buckets_x27_671_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v___x_685_; lean_object* v_buckets_x27_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
lean_inc(v_bkt_666_);
v___x_685_ = lean_box(0);
v_buckets_x27_686_ = lean_array_uset(v_buckets_648_, v___x_665_, v___x_685_);
v___x_687_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_645_, v_b_646_, v_bkt_666_);
v___x_688_ = lean_array_uset(v_buckets_x27_686_, v___x_665_, v___x_687_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_688_);
v___x_690_ = v___x_650_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_size_647_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(lean_object* v_as_695_, size_t v_sz_696_, size_t v_i_697_, lean_object* v_b_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_lt(v_i_697_, v_sz_696_);
if (v___x_699_ == 0)
{
return v_b_698_;
}
else
{
lean_object* v_a_700_; lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v_r_703_; size_t v___x_704_; size_t v___x_705_; 
v_a_700_ = lean_array_uget_borrowed(v_as_695_, v_i_697_);
v_fst_701_ = lean_ctor_get(v_a_700_, 0);
v_snd_702_ = lean_ctor_get(v_a_700_, 1);
lean_inc(v_snd_702_);
lean_inc(v_fst_701_);
v_r_703_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_b_698_, v_fst_701_, v_snd_702_);
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_697_, v___x_704_);
v_i_697_ = v___x_705_;
v_b_698_ = v_r_703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(lean_object* v_as_707_, lean_object* v_sz_708_, lean_object* v_i_709_, lean_object* v_b_710_){
_start:
{
size_t v_sz_boxed_711_; size_t v_i_boxed_712_; lean_object* v_res_713_; 
v_sz_boxed_711_ = lean_unbox_usize(v_sz_708_);
lean_dec(v_sz_708_);
v_i_boxed_712_ = lean_unbox_usize(v_i_709_);
lean_dec(v_i_709_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_707_, v_sz_boxed_711_, v_i_boxed_712_, v_b_710_);
lean_dec_ref(v_as_707_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object* v_m_714_, lean_object* v_l_715_){
_start:
{
size_t v_sz_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_sz_716_ = lean_array_size(v_l_715_);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_l_715_, v_sz_716_, v___x_717_, v_m_714_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object* v_m_719_, lean_object* v_l_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_719_, v_l_720_);
lean_dec_ref(v_l_720_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
v___x_723_ = lean_unsigned_to_nat(16u);
v___x_724_ = lean_mk_array(v___x_723_, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t v_pu_728_, lean_object* v_decls_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; size_t v_sz_749_; size_t v___x_750_; lean_object* v___x_751_; lean_object* v_declsMap_752_; lean_object* v___x_753_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_box(0);
v___x_737_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
v___x_738_ = lean_array_get_size(v_decls_729_);
v___x_739_ = lean_unsigned_to_nat(4u);
v___x_740_ = lean_nat_mul(v___x_738_, v___x_739_);
v___x_741_ = lean_unsigned_to_nat(3u);
v___x_742_ = lean_nat_div(v___x_740_, v___x_741_);
lean_dec(v___x_740_);
v___x_743_ = l_Nat_nextPowerOfTwo(v___x_742_);
lean_dec(v___x_742_);
v___x_744_ = lean_mk_array(v___x_743_, v___x_736_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_735_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_738_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_st_mk_ref(v___x_747_);
v_sz_749_ = lean_array_size(v_decls_729_);
v___x_750_ = ((size_t)0ULL);
lean_inc_ref(v_decls_729_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_749_, v___x_750_, v_decls_729_);
v_declsMap_752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_737_, v___x_751_);
lean_dec_ref(v___x_751_);
v___x_753_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_728_, v_decls_729_, v_declsMap_752_, v___x_748_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec_ref(v_declsMap_752_);
lean_dec_ref(v_decls_729_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_762_; 
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_763_);
v___x_755_ = v___x_753_;
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
else
{
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v_order_758_; lean_object* v___x_760_; 
v___x_757_ = lean_st_ref_get(v___x_748_);
lean_dec(v___x_748_);
v_order_758_ = lean_ctor_get(v___x_757_, 1);
lean_inc_ref(v_order_758_);
lean_dec(v___x_757_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_order_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_order_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v___x_748_);
v_a_764_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_753_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_753_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object* v_pu_772_, lean_object* v_decls_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
uint8_t v_pu_boxed_779_; lean_object* v_res_780_; 
v_pu_boxed_779_ = lean_unbox(v_pu_772_);
v_res_780_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_boxed_779_, v_decls_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object* v_00_u03b2_781_, lean_object* v_m_782_, lean_object* v_a_783_, lean_object* v_b_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_m_782_, v_a_783_, v_b_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_786_, lean_object* v_a_787_, lean_object* v_b_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_787_, v_b_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t v_pu_791_, lean_object* v_decls_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_791_, v_decls_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object* v_pu_799_, lean_object* v_decls_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_pu_boxed_806_; lean_object* v_res_807_; 
v_pu_boxed_806_ = lean_unbox(v_pu_799_);
v_res_807_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_boxed_806_, v_decls_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t v___x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v___x_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object* v___x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
uint8_t v___x_28__boxed_823_; lean_object* v_res_824_; 
v___x_28__boxed_823_ = lean_unbox(v___x_816_);
v_res_824_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_28__boxed_823_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_824_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_toposortPass___closed__2(void){
_start:
{
uint8_t v___x_828_; uint8_t v___x_829_; 
v___x_828_ = 2;
v___x_829_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__3(void){
_start:
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___f_832_; 
v___x_830_ = lean_uint8_once(&l_Lean_Compiler_LCNF_toposortPass___closed__2, &l_Lean_Compiler_LCNF_toposortPass___closed__2_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__2);
v___x_831_ = lean_box(v___x_830_);
v___f_832_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed), 7, 1);
lean_closure_set(v___f_832_, 0, v___x_831_);
return v___f_832_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__4(void){
_start:
{
lean_object* v___f_833_; lean_object* v___x_834_; uint8_t v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___f_833_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__3, &l_Lean_Compiler_LCNF_toposortPass___closed__3_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__3);
v___x_834_ = ((lean_object*)(l_Lean_Compiler_LCNF_toposortPass___closed__1));
v___x_835_ = 0;
v___x_836_ = 2;
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_834_);
lean_ctor_set(v___x_838_, 2, v___f_833_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*3, v___x_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*3 + 1, v___x_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*3 + 2, v___x_835_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass(void){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__4, &l_Lean_Compiler_LCNF_toposortPass___closed__4_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__4);
return v___x_839_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_toposortPass = _init_l_Lean_Compiler_LCNF_toposortPass();
lean_mark_persistent(l_Lean_Compiler_LCNF_toposortPass);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Toposort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Toposort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Toposort(builtin);
}
#ifdef __cplusplus
}
#endif
