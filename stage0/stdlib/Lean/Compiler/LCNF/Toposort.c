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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_253_ = lean_st_ref_set(v_a_214_, v___x_252_);
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
v___x_231_ = lean_st_ref_set(v___y_221_, v___x_230_);
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
lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_394_; 
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_341_, 0);
lean_dec(v_unused_395_);
v___x_343_ = v___x_341_;
v_isShared_344_ = v_isSharedCheck_394_;
goto v_resetjp_342_;
}
else
{
lean_dec(v___x_341_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_394_;
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
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_le(v___x_360_, v___x_360_);
if (v___x_366_ == 0)
{
if (v___x_362_ == 0)
{
lean_object* v___x_368_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_361_);
v___x_368_ = v___x_343_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_361_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
lean_del_object(v___x_343_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_360_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_331_, v_pu_332_, v_alts_358_, v___x_370_, v___x_371_, v___x_361_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_372_;
}
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
lean_del_object(v___x_343_);
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_360_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_331_, v_pu_332_, v_alts_358_, v___x_373_, v___x_374_, v___x_361_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_375_;
}
}
}
case 7:
{
lean_object* v_k_376_; 
lean_del_object(v___x_343_);
v_k_376_ = lean_ctor_get(v_c_333_, 3);
v_c_333_ = v_k_376_;
goto _start;
}
case 8:
{
lean_object* v_k_378_; 
lean_del_object(v___x_343_);
v_k_378_ = lean_ctor_get(v_c_333_, 3);
v_c_333_ = v_k_378_;
goto _start;
}
case 9:
{
lean_object* v_k_380_; 
lean_del_object(v___x_343_);
v_k_380_ = lean_ctor_get(v_c_333_, 5);
v_c_333_ = v_k_380_;
goto _start;
}
case 10:
{
lean_object* v_k_382_; 
lean_del_object(v___x_343_);
v_k_382_ = lean_ctor_get(v_c_333_, 2);
v_c_333_ = v_k_382_;
goto _start;
}
case 11:
{
lean_object* v_k_384_; 
lean_del_object(v___x_343_);
v_k_384_ = lean_ctor_get(v_c_333_, 2);
v_c_333_ = v_k_384_;
goto _start;
}
case 12:
{
lean_object* v_k_386_; 
lean_del_object(v___x_343_);
v_k_386_ = lean_ctor_get(v_c_333_, 3);
v_c_333_ = v_k_386_;
goto _start;
}
case 13:
{
lean_object* v_k_388_; 
lean_del_object(v___x_343_);
v_k_388_ = lean_ctor_get(v_c_333_, 1);
v_c_333_ = v_k_388_;
goto _start;
}
default: 
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_box(0);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_390_);
v___x_392_ = v___x_343_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t v_pu_396_, lean_object* v_x_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_396_, v_pu_396_, v_x_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object* v_pu_406_, lean_object* v_declName_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
uint8_t v_pu_boxed_415_; lean_object* v_res_416_; 
v_pu_boxed_415_ = lean_unbox(v_pu_406_);
v_res_416_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_boxed_415_, v_declName_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_declName_407_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object* v_pu_417_, lean_object* v_code_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
uint8_t v_pu_boxed_426_; lean_object* v_res_427_; 
v_pu_boxed_426_ = lean_unbox(v_pu_417_);
v_res_427_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_boxed_426_, v_code_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_code_418_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object* v_pu_428_, lean_object* v_pu_429_, lean_object* v_as_430_, lean_object* v_i_431_, lean_object* v_stop_432_, lean_object* v_b_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_pu_boxed_441_; uint8_t v_pu_boxed_442_; size_t v_i_boxed_443_; size_t v_stop_boxed_444_; lean_object* v_res_445_; 
v_pu_boxed_441_ = lean_unbox(v_pu_428_);
v_pu_boxed_442_ = lean_unbox(v_pu_429_);
v_i_boxed_443_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_stop_boxed_444_ = lean_unbox_usize(v_stop_432_);
lean_dec(v_stop_432_);
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_441_, v_pu_boxed_442_, v_as_430_, v_i_boxed_443_, v_stop_boxed_444_, v_b_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v_as_430_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object* v_pu_446_, lean_object* v_decl_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
uint8_t v_pu_boxed_455_; lean_object* v_res_456_; 
v_pu_boxed_455_ = lean_unbox(v_pu_446_);
v_res_456_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_boxed_455_, v_decl_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object* v_pu_457_, lean_object* v_pu_458_, lean_object* v_c_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v_pu_boxed_467_; uint8_t v_pu_boxed_468_; lean_object* v_res_469_; 
v_pu_boxed_467_ = lean_unbox(v_pu_457_);
v_pu_boxed_468_ = lean_unbox(v_pu_458_);
v_res_469_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_467_, v_pu_boxed_468_, v_c_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v_c_459_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(uint8_t v_pu_470_, lean_object* v_f_471_, lean_object* v_v_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_471_, v_v_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object* v_pu_481_, lean_object* v_f_482_, lean_object* v_v_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
uint8_t v_pu_boxed_491_; lean_object* v_res_492_; 
v_pu_boxed_491_ = lean_unbox(v_pu_481_);
v_res_492_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_boxed_491_, v_f_482_, v_v_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_492_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object* v_00_u03b2_493_, lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_494_, v_a_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object* v_00_u03b2_497_, lean_object* v_m_498_, lean_object* v_a_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_497_, v_m_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_m_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(lean_object* v_00_u03b2_502_, lean_object* v_m_503_, lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_m_503_, v_a_504_, v_b_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(lean_object* v_00_u03b2_507_, lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_508_, v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(lean_object* v_00_u03b2_511_, lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(v_00_u03b2_511_, v_m_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_m_512_);
return v_res_514_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object* v_00_u03b2_515_, lean_object* v_a_516_, lean_object* v_x_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object* v_00_u03b2_519_, lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_519_, v_a_520_, v_x_521_);
lean_dec(v_x_521_);
lean_dec(v_a_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(lean_object* v_00_u03b2_524_, lean_object* v_data_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_data_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(lean_object* v_00_u03b2_531_, lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(v_00_u03b2_531_, v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec(v_a_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_535_, lean_object* v_i_536_, lean_object* v_source_537_, lean_object* v_target_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v_i_536_, v_source_537_, v_target_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t v_pu_544_, lean_object* v_as_545_, size_t v_i_546_, size_t v_stop_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_eq(v_i_546_, v_stop_547_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_array_uget_borrowed(v_as_545_, v_i_546_);
lean_inc(v___x_557_);
v___x_558_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_544_, v___x_557_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; size_t v___x_560_; size_t v___x_561_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_546_, v___x_560_);
v_i_546_ = v___x_561_;
v_b_548_ = v_a_559_;
goto _start;
}
else
{
return v___x_558_;
}
}
else
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_b_548_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object* v_pu_564_, lean_object* v_as_565_, lean_object* v_i_566_, lean_object* v_stop_567_, lean_object* v_b_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v_pu_boxed_576_; size_t v_i_boxed_577_; size_t v_stop_boxed_578_; lean_object* v_res_579_; 
v_pu_boxed_576_ = lean_unbox(v_pu_564_);
v_i_boxed_577_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_stop_boxed_578_ = lean_unbox_usize(v_stop_567_);
lean_dec(v_stop_567_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_576_, v_as_565_, v_i_boxed_577_, v_stop_boxed_578_, v_b_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v_as_565_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t v_pu_580_, lean_object* v_decls_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_array_get_size(v_decls_581_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_nat_dec_lt(v___x_589_, v___x_590_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
return v___x_593_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = lean_nat_dec_le(v___x_590_, v___x_590_);
if (v___x_594_ == 0)
{
if (v___x_592_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_591_);
return v___x_595_;
}
else
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_596_ = ((size_t)0ULL);
v___x_597_ = lean_usize_of_nat(v___x_590_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_580_, v_decls_581_, v___x_596_, v___x_597_, v___x_591_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_598_;
}
}
else
{
size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_590_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_580_, v_decls_581_, v___x_599_, v___x_600_, v___x_591_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object* v_pu_602_, lean_object* v_decls_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
uint8_t v_pu_boxed_611_; lean_object* v_res_612_; 
v_pu_boxed_611_ = lean_unbox(v_pu_602_);
v_res_612_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_boxed_611_, v_decls_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec_ref(v_decls_603_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t v_sz_613_, size_t v_i_614_, lean_object* v_bs_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_616_ == 0)
{
return v_bs_615_;
}
else
{
lean_object* v_v_617_; lean_object* v_toSignature_618_; lean_object* v_name_619_; lean_object* v___x_620_; lean_object* v_bs_x27_621_; lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_v_617_ = lean_array_uget(v_bs_615_, v_i_614_);
v_toSignature_618_ = lean_ctor_get(v_v_617_, 0);
v_name_619_ = lean_ctor_get(v_toSignature_618_, 0);
lean_inc(v_name_619_);
v___x_620_ = lean_unsigned_to_nat(0u);
v_bs_x27_621_ = lean_array_uset(v_bs_615_, v_i_614_, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_name_619_);
lean_ctor_set(v___x_622_, 1, v_v_617_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_614_, v___x_623_);
v___x_625_ = lean_array_uset(v_bs_x27_621_, v_i_614_, v___x_622_);
v_i_614_ = v___x_624_;
v_bs_615_ = v___x_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object* v_sz_627_, lean_object* v_i_628_, lean_object* v_bs_629_){
_start:
{
size_t v_sz_boxed_630_; size_t v_i_boxed_631_; lean_object* v_res_632_; 
v_sz_boxed_630_ = lean_unbox_usize(v_sz_627_);
lean_dec(v_sz_627_);
v_i_boxed_631_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_630_, v_i_boxed_631_, v_bs_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(lean_object* v_a_633_, lean_object* v_b_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_dec(v_b_634_);
lean_dec(v_a_633_);
return v_x_635_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_650_; 
v_key_636_ = lean_ctor_get(v_x_635_, 0);
v_value_637_ = lean_ctor_get(v_x_635_, 1);
v_tail_638_ = lean_ctor_get(v_x_635_, 2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_650_ == 0)
{
v___x_640_ = v_x_635_;
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_value_637_);
lean_inc(v_key_636_);
lean_dec(v_x_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = lean_name_eq(v_key_636_, v_a_633_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_633_, v_b_634_, v_tail_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v___x_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_value_637_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v_value_637_);
lean_dec(v_key_636_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_b_634_);
lean_ctor_set(v___x_640_, 0, v_a_633_);
v___x_648_ = v___x_640_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_633_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_b_634_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_tail_638_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(lean_object* v_m_651_, lean_object* v_a_652_, lean_object* v_b_653_){
_start:
{
lean_object* v_size_654_; lean_object* v_buckets_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_701_; 
v_size_654_ = lean_ctor_get(v_m_651_, 0);
v_buckets_655_ = lean_ctor_get(v_m_651_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_m_651_);
if (v_isSharedCheck_701_ == 0)
{
v___x_657_ = v_m_651_;
v_isShared_658_ = v_isSharedCheck_701_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_buckets_655_);
lean_inc(v_size_654_);
lean_dec(v_m_651_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_701_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; uint64_t v___y_661_; 
v___x_659_ = lean_array_get_size(v_buckets_655_);
if (lean_obj_tag(v_a_652_) == 0)
{
uint64_t v___x_699_; 
v___x_699_ = 1723ULL;
v___y_661_ = v___x_699_;
goto v___jp_660_;
}
else
{
uint64_t v_hash_700_; 
v_hash_700_ = lean_ctor_get_uint64(v_a_652_, sizeof(void*)*2);
v___y_661_ = v_hash_700_;
goto v___jp_660_;
}
v___jp_660_:
{
uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v_fold_664_; uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v_bkt_673_; uint8_t v___x_674_; 
v___x_662_ = 32ULL;
v___x_663_ = lean_uint64_shift_right(v___y_661_, v___x_662_);
v_fold_664_ = lean_uint64_xor(v___y_661_, v___x_663_);
v___x_665_ = 16ULL;
v___x_666_ = lean_uint64_shift_right(v_fold_664_, v___x_665_);
v___x_667_ = lean_uint64_xor(v_fold_664_, v___x_666_);
v___x_668_ = lean_uint64_to_usize(v___x_667_);
v___x_669_ = lean_usize_of_nat(v___x_659_);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_sub(v___x_669_, v___x_670_);
v___x_672_ = lean_usize_land(v___x_668_, v___x_671_);
v_bkt_673_ = lean_array_uget_borrowed(v_buckets_655_, v___x_672_);
v___x_674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_652_, v_bkt_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v_size_x27_676_; lean_object* v___x_677_; lean_object* v_buckets_x27_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v_size_x27_676_ = lean_nat_add(v_size_654_, v___x_675_);
lean_dec(v_size_654_);
lean_inc(v_bkt_673_);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v_a_652_);
lean_ctor_set(v___x_677_, 1, v_b_653_);
lean_ctor_set(v___x_677_, 2, v_bkt_673_);
v_buckets_x27_678_ = lean_array_uset(v_buckets_655_, v___x_672_, v___x_677_);
v___x_679_ = lean_unsigned_to_nat(4u);
v___x_680_ = lean_nat_mul(v_size_x27_676_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(3u);
v___x_682_ = lean_nat_div(v___x_680_, v___x_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_array_get_size(v_buckets_x27_678_);
v___x_684_ = lean_nat_dec_le(v___x_682_, v___x_683_);
lean_dec(v___x_682_);
if (v___x_684_ == 0)
{
lean_object* v_val_685_; lean_object* v___x_687_; 
v_val_685_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_678_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_val_685_);
lean_ctor_set(v___x_657_, 0, v_size_x27_676_);
v___x_687_ = v___x_657_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_size_x27_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_val_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v___x_690_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_buckets_x27_678_);
lean_ctor_set(v___x_657_, 0, v_size_x27_676_);
v___x_690_ = v___x_657_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_size_x27_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_buckets_x27_678_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v___x_692_; lean_object* v_buckets_x27_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_inc(v_bkt_673_);
v___x_692_ = lean_box(0);
v_buckets_x27_693_ = lean_array_uset(v_buckets_655_, v___x_672_, v___x_692_);
v___x_694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_652_, v_b_653_, v_bkt_673_);
v___x_695_ = lean_array_uset(v_buckets_x27_693_, v___x_672_, v___x_694_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_695_);
v___x_697_ = v___x_657_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_size_654_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(lean_object* v_as_702_, size_t v_sz_703_, size_t v_i_704_, lean_object* v_b_705_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_706_ == 0)
{
return v_b_705_;
}
else
{
lean_object* v_a_707_; lean_object* v_fst_708_; lean_object* v_snd_709_; lean_object* v_r_710_; size_t v___x_711_; size_t v___x_712_; 
v_a_707_ = lean_array_uget_borrowed(v_as_702_, v_i_704_);
v_fst_708_ = lean_ctor_get(v_a_707_, 0);
v_snd_709_ = lean_ctor_get(v_a_707_, 1);
lean_inc(v_snd_709_);
lean_inc(v_fst_708_);
v_r_710_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_b_705_, v_fst_708_, v_snd_709_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_704_, v___x_711_);
v_i_704_ = v___x_712_;
v_b_705_ = v_r_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(lean_object* v_as_714_, lean_object* v_sz_715_, lean_object* v_i_716_, lean_object* v_b_717_){
_start:
{
size_t v_sz_boxed_718_; size_t v_i_boxed_719_; lean_object* v_res_720_; 
v_sz_boxed_718_ = lean_unbox_usize(v_sz_715_);
lean_dec(v_sz_715_);
v_i_boxed_719_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_714_, v_sz_boxed_718_, v_i_boxed_719_, v_b_717_);
lean_dec_ref(v_as_714_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object* v_m_721_, lean_object* v_l_722_){
_start:
{
size_t v_sz_723_; size_t v___x_724_; lean_object* v___x_725_; 
v_sz_723_ = lean_array_size(v_l_722_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_l_722_, v_sz_723_, v___x_724_, v_m_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object* v_m_726_, lean_object* v_l_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_726_, v_l_727_);
lean_dec_ref(v_l_727_);
return v_res_728_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = lean_unsigned_to_nat(16u);
v___x_731_ = lean_mk_array(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t v_pu_735_, lean_object* v_decls_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; size_t v_sz_756_; size_t v___x_757_; lean_object* v___x_758_; lean_object* v_declsMap_759_; lean_object* v___x_760_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_box(0);
v___x_744_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
v___x_745_ = lean_array_get_size(v_decls_736_);
v___x_746_ = lean_unsigned_to_nat(4u);
v___x_747_ = lean_nat_mul(v___x_745_, v___x_746_);
v___x_748_ = lean_unsigned_to_nat(3u);
v___x_749_ = lean_nat_div(v___x_747_, v___x_748_);
lean_dec(v___x_747_);
v___x_750_ = l_Nat_nextPowerOfTwo(v___x_749_);
lean_dec(v___x_749_);
v___x_751_ = lean_mk_array(v___x_750_, v___x_743_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_742_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_mk_empty_array_with_capacity(v___x_745_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_st_mk_ref(v___x_754_);
v_sz_756_ = lean_array_size(v_decls_736_);
v___x_757_ = ((size_t)0ULL);
lean_inc_ref(v_decls_736_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_756_, v___x_757_, v_decls_736_);
v_declsMap_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_744_, v___x_758_);
lean_dec_ref(v___x_758_);
v___x_760_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_735_, v_decls_736_, v_declsMap_759_, v___x_755_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec_ref(v_declsMap_759_);
lean_dec_ref(v_decls_736_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_769_; 
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_760_, 0);
lean_dec(v_unused_770_);
v___x_762_ = v___x_760_;
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
else
{
lean_dec(v___x_760_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v_order_765_; lean_object* v___x_767_; 
v___x_764_ = lean_st_ref_get(v___x_755_);
lean_dec(v___x_755_);
v_order_765_ = lean_ctor_get(v___x_764_, 1);
lean_inc_ref(v_order_765_);
lean_dec(v___x_764_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_order_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_order_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v___x_755_);
v_a_771_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_760_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_760_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object* v_pu_779_, lean_object* v_decls_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
uint8_t v_pu_boxed_786_; lean_object* v_res_787_; 
v_pu_boxed_786_ = lean_unbox(v_pu_779_);
v_res_787_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_boxed_786_, v_decls_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_m_789_, lean_object* v_a_790_, lean_object* v_b_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_m_789_, v_a_790_, v_b_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_793_, lean_object* v_a_794_, lean_object* v_b_795_, lean_object* v_x_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_794_, v_b_795_, v_x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t v_pu_798_, lean_object* v_decls_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_798_, v_decls_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object* v_pu_806_, lean_object* v_decls_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_pu_boxed_813_; lean_object* v_res_814_; 
v_pu_boxed_813_ = lean_unbox(v_pu_806_);
v_res_814_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_boxed_813_, v_decls_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t v___x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v___x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object* v___x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_28__boxed_830_; lean_object* v_res_831_; 
v___x_28__boxed_830_ = lean_unbox(v___x_823_);
v_res_831_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_28__boxed_830_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_831_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_toposortPass___closed__2(void){
_start:
{
uint8_t v___x_835_; uint8_t v___x_836_; 
v___x_835_ = 2;
v___x_836_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__3(void){
_start:
{
uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___f_839_; 
v___x_837_ = lean_uint8_once(&l_Lean_Compiler_LCNF_toposortPass___closed__2, &l_Lean_Compiler_LCNF_toposortPass___closed__2_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__2);
v___x_838_ = lean_box(v___x_837_);
v___f_839_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed), 7, 1);
lean_closure_set(v___f_839_, 0, v___x_838_);
return v___f_839_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__4(void){
_start:
{
lean_object* v___f_840_; lean_object* v___x_841_; uint8_t v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___f_840_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__3, &l_Lean_Compiler_LCNF_toposortPass___closed__3_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__3);
v___x_841_ = ((lean_object*)(l_Lean_Compiler_LCNF_toposortPass___closed__1));
v___x_842_ = 0;
v___x_843_ = 2;
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_841_);
lean_ctor_set(v___x_845_, 2, v___f_840_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*3, v___x_843_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*3 + 1, v___x_843_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*3 + 2, v___x_842_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass(void){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__4, &l_Lean_Compiler_LCNF_toposortPass___closed__4_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__4);
return v___x_846_;
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
