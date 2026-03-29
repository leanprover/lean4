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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0;
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
lean_dec_ref(v_v_2_);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_42_; uint64_t v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1723u);
v___x_43_ = lean_uint64_of_nat(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
return v_x_44_;
}
else
{
lean_object* v_key_46_; lean_object* v_value_47_; lean_object* v_tail_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_74_; 
v_key_46_ = lean_ctor_get(v_x_45_, 0);
v_value_47_ = lean_ctor_get(v_x_45_, 1);
v_tail_48_ = lean_ctor_get(v_x_45_, 2);
v_isSharedCheck_74_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_74_ == 0)
{
v___x_50_ = v_x_45_;
v_isShared_51_ = v_isSharedCheck_74_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_tail_48_);
lean_inc(v_value_47_);
lean_inc(v_key_46_);
lean_dec(v_x_45_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_74_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; uint64_t v___y_54_; 
v___x_52_ = lean_array_get_size(v_x_44_);
if (lean_obj_tag(v_key_46_) == 0)
{
uint64_t v___x_72_; 
v___x_72_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_54_ = v___x_72_;
goto v___jp_53_;
}
else
{
uint64_t v_hash_73_; 
v_hash_73_ = lean_ctor_get_uint64(v_key_46_, sizeof(void*)*2);
v___y_54_ = v_hash_73_;
goto v___jp_53_;
}
v___jp_53_:
{
uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v_fold_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; size_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_55_ = 32ULL;
v___x_56_ = lean_uint64_shift_right(v___y_54_, v___x_55_);
v_fold_57_ = lean_uint64_xor(v___y_54_, v___x_56_);
v___x_58_ = 16ULL;
v___x_59_ = lean_uint64_shift_right(v_fold_57_, v___x_58_);
v___x_60_ = lean_uint64_xor(v_fold_57_, v___x_59_);
v___x_61_ = lean_uint64_to_usize(v___x_60_);
v___x_62_ = lean_usize_of_nat(v___x_52_);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_sub(v___x_62_, v___x_63_);
v___x_65_ = lean_usize_land(v___x_61_, v___x_64_);
v___x_66_ = lean_array_uget_borrowed(v_x_44_, v___x_65_);
lean_inc(v___x_66_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v___x_66_);
v___x_68_ = v___x_50_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_key_46_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_value_47_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v___x_66_);
v___x_68_ = v_reuseFailAlloc_71_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; 
v___x_69_ = lean_array_uset(v_x_44_, v___x_65_, v___x_68_);
v_x_44_ = v___x_69_;
v_x_45_ = v_tail_48_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(lean_object* v_i_75_, lean_object* v_source_76_, lean_object* v_target_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_array_get_size(v_source_76_);
v___x_79_ = lean_nat_dec_lt(v_i_75_, v___x_78_);
if (v___x_79_ == 0)
{
lean_dec_ref(v_source_76_);
lean_dec(v_i_75_);
return v_target_77_;
}
else
{
lean_object* v_es_80_; lean_object* v___x_81_; lean_object* v_source_82_; lean_object* v_target_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_es_80_ = lean_array_fget(v_source_76_, v_i_75_);
v___x_81_ = lean_box(0);
v_source_82_ = lean_array_fset(v_source_76_, v_i_75_, v___x_81_);
v_target_83_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_target_77_, v_es_80_);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_add(v_i_75_, v___x_84_);
lean_dec(v_i_75_);
v_i_75_ = v___x_85_;
v_source_76_ = v_source_82_;
v_target_77_ = v_target_83_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(lean_object* v_data_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_nbuckets_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_88_ = lean_array_get_size(v_data_87_);
v___x_89_ = lean_unsigned_to_nat(2u);
v_nbuckets_90_ = lean_nat_mul(v___x_88_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_box(0);
v___x_93_ = lean_mk_array(v_nbuckets_90_, v___x_92_);
v___x_94_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v___x_91_, v_data_87_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object* v_m_95_, lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
lean_object* v_size_98_; lean_object* v_buckets_99_; lean_object* v___x_100_; uint64_t v___y_102_; 
v_size_98_ = lean_ctor_get(v_m_95_, 0);
v_buckets_99_ = lean_ctor_get(v_m_95_, 1);
v___x_100_ = lean_array_get_size(v_buckets_99_);
if (lean_obj_tag(v_a_96_) == 0)
{
uint64_t v___x_139_; 
v___x_139_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_102_ = v___x_139_;
goto v___jp_101_;
}
else
{
uint64_t v_hash_140_; 
v_hash_140_ = lean_ctor_get_uint64(v_a_96_, sizeof(void*)*2);
v___y_102_ = v_hash_140_;
goto v___jp_101_;
}
v___jp_101_:
{
uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v_fold_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v_bkt_114_; uint8_t v___x_115_; 
v___x_103_ = 32ULL;
v___x_104_ = lean_uint64_shift_right(v___y_102_, v___x_103_);
v_fold_105_ = lean_uint64_xor(v___y_102_, v___x_104_);
v___x_106_ = 16ULL;
v___x_107_ = lean_uint64_shift_right(v_fold_105_, v___x_106_);
v___x_108_ = lean_uint64_xor(v_fold_105_, v___x_107_);
v___x_109_ = lean_uint64_to_usize(v___x_108_);
v___x_110_ = lean_usize_of_nat(v___x_100_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_sub(v___x_110_, v___x_111_);
v___x_113_ = lean_usize_land(v___x_109_, v___x_112_);
v_bkt_114_ = lean_array_uget_borrowed(v_buckets_99_, v___x_113_);
v___x_115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_96_, v_bkt_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_136_; 
lean_inc_ref(v_buckets_99_);
lean_inc(v_size_98_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_m_95_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; lean_object* v_unused_138_; 
v_unused_137_ = lean_ctor_get(v_m_95_, 1);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_m_95_, 0);
lean_dec(v_unused_138_);
v___x_117_ = v_m_95_;
v_isShared_118_ = v_isSharedCheck_136_;
goto v_resetjp_116_;
}
else
{
lean_dec(v_m_95_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_136_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v_size_x27_120_; lean_object* v___x_121_; lean_object* v_buckets_x27_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v_size_x27_120_ = lean_nat_add(v_size_98_, v___x_119_);
lean_dec(v_size_98_);
lean_inc(v_bkt_114_);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v_a_96_);
lean_ctor_set(v___x_121_, 1, v_b_97_);
lean_ctor_set(v___x_121_, 2, v_bkt_114_);
v_buckets_x27_122_ = lean_array_uset(v_buckets_99_, v___x_113_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(4u);
v___x_124_ = lean_nat_mul(v_size_x27_120_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(3u);
v___x_126_ = lean_nat_div(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_array_get_size(v_buckets_x27_122_);
v___x_128_ = lean_nat_dec_le(v___x_126_, v___x_127_);
lean_dec(v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v_val_129_; lean_object* v___x_131_; 
v_val_129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_122_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_val_129_);
lean_ctor_set(v___x_117_, 0, v_size_x27_120_);
v___x_131_ = v___x_117_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_val_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_134_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_buckets_x27_122_);
lean_ctor_set(v___x_117_, 0, v_size_x27_120_);
v___x_134_ = v___x_117_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_buckets_x27_122_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_dec(v_b_97_);
lean_dec(v_a_96_);
return v_m_95_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object* v_m_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_buckets_143_; lean_object* v___x_144_; uint64_t v___y_146_; 
v_buckets_143_ = lean_ctor_get(v_m_141_, 1);
v___x_144_ = lean_array_get_size(v_buckets_143_);
if (lean_obj_tag(v_a_142_) == 0)
{
uint64_t v___x_160_; 
v___x_160_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_146_ = v___x_160_;
goto v___jp_145_;
}
else
{
uint64_t v_hash_161_; 
v_hash_161_ = lean_ctor_get_uint64(v_a_142_, sizeof(void*)*2);
v___y_146_ = v_hash_161_;
goto v___jp_145_;
}
v___jp_145_:
{
uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v_fold_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_147_ = 32ULL;
v___x_148_ = lean_uint64_shift_right(v___y_146_, v___x_147_);
v_fold_149_ = lean_uint64_xor(v___y_146_, v___x_148_);
v___x_150_ = 16ULL;
v___x_151_ = lean_uint64_shift_right(v_fold_149_, v___x_150_);
v___x_152_ = lean_uint64_xor(v_fold_149_, v___x_151_);
v___x_153_ = lean_uint64_to_usize(v___x_152_);
v___x_154_ = lean_usize_of_nat(v___x_144_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v___x_154_, v___x_155_);
v___x_157_ = lean_usize_land(v___x_153_, v___x_156_);
v___x_158_ = lean_array_uget_borrowed(v_buckets_143_, v___x_157_);
v___x_159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_142_, v___x_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_m_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(lean_object* v_a_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v_key_169_; lean_object* v_value_170_; lean_object* v_tail_171_; uint8_t v___x_172_; 
v_key_169_ = lean_ctor_get(v_x_167_, 0);
v_value_170_ = lean_ctor_get(v_x_167_, 1);
v_tail_171_ = lean_ctor_get(v_x_167_, 2);
v___x_172_ = lean_name_eq(v_key_169_, v_a_166_);
if (v___x_172_ == 0)
{
v_x_167_ = v_tail_171_;
goto _start;
}
else
{
lean_object* v___x_174_; 
lean_inc(v_value_170_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_value_170_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg___boxed(lean_object* v_a_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_175_, v_x_176_);
lean_dec(v_x_176_);
lean_dec(v_a_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(lean_object* v_m_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_buckets_180_; lean_object* v___x_181_; uint64_t v___y_183_; 
v_buckets_180_ = lean_ctor_get(v_m_178_, 1);
v___x_181_ = lean_array_get_size(v_buckets_180_);
if (lean_obj_tag(v_a_179_) == 0)
{
uint64_t v___x_197_; 
v___x_197_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_183_ = v___x_197_;
goto v___jp_182_;
}
else
{
uint64_t v_hash_198_; 
v_hash_198_ = lean_ctor_get_uint64(v_a_179_, sizeof(void*)*2);
v___y_183_ = v_hash_198_;
goto v___jp_182_;
}
v___jp_182_:
{
uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v_fold_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_184_ = 32ULL;
v___x_185_ = lean_uint64_shift_right(v___y_183_, v___x_184_);
v_fold_186_ = lean_uint64_xor(v___y_183_, v___x_185_);
v___x_187_ = 16ULL;
v___x_188_ = lean_uint64_shift_right(v_fold_186_, v___x_187_);
v___x_189_ = lean_uint64_xor(v_fold_186_, v___x_188_);
v___x_190_ = lean_uint64_to_usize(v___x_189_);
v___x_191_ = lean_usize_of_nat(v___x_181_);
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_sub(v___x_191_, v___x_192_);
v___x_194_ = lean_usize_land(v___x_190_, v___x_193_);
v___x_195_ = lean_array_uget_borrowed(v_buckets_180_, v___x_194_);
v___x_196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_179_, v___x_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg___boxed(lean_object* v_m_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_m_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(lean_object* v_pu_202_, lean_object* v_x_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
uint8_t v_pu_boxed_211_; lean_object* v_res_212_; 
v_pu_boxed_211_ = lean_unbox(v_pu_202_);
v_res_212_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(v_pu_boxed_211_, v_x_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec_ref(v_x_203_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(uint8_t v_pu_213_, lean_object* v_decl_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___y_223_; lean_object* v___x_238_; lean_object* v_toSignature_239_; lean_object* v_seen_240_; lean_object* v_value_241_; lean_object* v_name_242_; uint8_t v___x_243_; 
v___x_238_ = lean_st_ref_get(v_a_216_);
v_toSignature_239_ = lean_ctor_get(v_decl_214_, 0);
v_seen_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_seen_240_);
lean_dec(v___x_238_);
v_value_241_ = lean_ctor_get(v_decl_214_, 1);
v_name_242_ = lean_ctor_get(v_toSignature_239_, 0);
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_seen_240_, v_name_242_);
lean_dec_ref(v_seen_240_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_seen_246_; lean_object* v_order_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_267_; 
v___x_244_ = lean_st_ref_get(v_a_220_);
v___x_245_ = lean_st_ref_take(v_a_216_);
v_seen_246_ = lean_ctor_get(v___x_245_, 0);
v_order_247_ = lean_ctor_get(v___x_245_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_267_ == 0)
{
v___x_249_ = v___x_245_;
v_isShared_250_ = v_isSharedCheck_267_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_order_247_);
lean_inc(v_seen_246_);
lean_dec(v___x_245_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_267_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_251_ = lean_box(0);
lean_inc(v_name_242_);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_seen_246_, v_name_242_, v___x_251_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_252_);
v___x_254_ = v___x_249_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_order_247_);
v___x_254_ = v_reuseFailAlloc_266_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___f_257_; lean_object* v___x_258_; 
v___x_255_ = lean_st_ref_set(v_a_216_, v___x_254_);
v___x_256_ = lean_box(v_pu_213_);
v___f_257_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed), 9, 1);
lean_closure_set(v___f_257_, 0, v___x_256_);
lean_inc_ref(v_value_241_);
v___x_258_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___f_257_, v_value_241_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___y_260_; lean_object* v_env_263_; lean_object* v___x_264_; 
lean_dec_ref(v___x_258_);
v_env_263_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref_n(v_env_263_, 2);
lean_dec(v___x_244_);
lean_inc(v_name_242_);
v___x_264_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_263_, v_name_242_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
lean_inc(v_name_242_);
v___x_265_ = lean_get_init_fn_name_for(v_env_263_, v_name_242_);
v___y_260_ = v___x_265_;
goto v___jp_259_;
}
else
{
lean_dec_ref(v_env_263_);
v___y_260_ = v___x_264_;
goto v___jp_259_;
}
v___jp_259_:
{
if (lean_obj_tag(v___y_260_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_262_; 
v_val_261_ = lean_ctor_get(v___y_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref(v___y_260_);
v___x_262_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_213_, v_val_261_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_val_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_dec_ref(v___x_262_);
v___y_223_ = v_a_216_;
goto v___jp_222_;
}
else
{
lean_dec_ref(v_decl_214_);
return v___x_262_;
}
}
else
{
lean_dec(v___y_260_);
v___y_223_ = v_a_216_;
goto v___jp_222_;
}
}
}
else
{
lean_dec(v___x_244_);
lean_dec_ref(v_decl_214_);
return v___x_258_;
}
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v_decl_214_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v_seen_225_; lean_object* v_order_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_237_; 
v___x_224_ = lean_st_ref_take(v___y_223_);
v_seen_225_ = lean_ctor_get(v___x_224_, 0);
v_order_226_ = lean_ctor_get(v___x_224_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_237_ == 0)
{
v___x_228_ = v___x_224_;
v_isShared_229_ = v_isSharedCheck_237_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_order_226_);
lean_inc(v_seen_225_);
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_237_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_array_push(v_order_226_, v_decl_214_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_seen_225_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_st_ref_set(v___y_223_, v___x_232_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(uint8_t v_pu_270_, lean_object* v_declName_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_a_272_, v_declName_271_);
if (lean_obj_tag(v___x_279_) == 1)
{
lean_object* v_val_280_; lean_object* v___x_281_; 
v_val_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref(v___x_279_);
v___x_281_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_270_, v_val_280_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(uint8_t v_pu_284_, lean_object* v_code_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
if (lean_obj_tag(v_code_285_) == 0)
{
lean_object* v_decl_293_; lean_object* v_value_294_; 
v_decl_293_ = lean_ctor_get(v_code_285_, 0);
v_value_294_ = lean_ctor_get(v_decl_293_, 3);
switch(lean_obj_tag(v_value_294_))
{
case 3:
{
lean_object* v_declName_295_; lean_object* v___x_296_; 
v_declName_295_ = lean_ctor_get(v_value_294_, 0);
v___x_296_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_284_, v_declName_295_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_296_;
}
case 9:
{
lean_object* v_fn_297_; lean_object* v___x_298_; 
v_fn_297_ = lean_ctor_get(v_value_294_, 0);
v___x_298_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_284_, v_fn_297_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_298_;
}
case 10:
{
lean_object* v_fn_299_; lean_object* v___x_300_; 
v_fn_299_ = lean_ctor_get(v_value_294_, 0);
v___x_300_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_284_, v_fn_299_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_300_;
}
default: 
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(uint8_t v_pu_305_, uint8_t v_pu_306_, lean_object* v_as_307_, size_t v_i_308_, size_t v_stop_309_, lean_object* v_b_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___y_319_; uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_eq(v_i_308_, v_stop_309_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_array_uget_borrowed(v_as_307_, v_i_308_);
switch(lean_obj_tag(v___x_325_))
{
case 0:
{
lean_object* v_code_326_; lean_object* v___x_327_; 
v_code_326_ = lean_ctor_get(v___x_325_, 2);
v___x_327_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_305_, v_pu_306_, v_code_326_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v___y_319_ = v___x_327_;
goto v___jp_318_;
}
case 1:
{
lean_object* v_code_328_; lean_object* v___x_329_; 
v_code_328_ = lean_ctor_get(v___x_325_, 1);
v___x_329_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_305_, v_pu_306_, v_code_328_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v___y_319_ = v___x_329_;
goto v___jp_318_;
}
default: 
{
lean_object* v_code_330_; lean_object* v___x_331_; 
v_code_330_ = lean_ctor_get(v___x_325_, 0);
v___x_331_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_305_, v_pu_306_, v_code_330_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v___y_319_ = v___x_331_;
goto v___jp_318_;
}
}
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_b_310_);
return v___x_332_;
}
v___jp_318_:
{
if (lean_obj_tag(v___y_319_) == 0)
{
lean_object* v_a_320_; size_t v___x_321_; size_t v___x_322_; 
v_a_320_ = lean_ctor_get(v___y_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v___y_319_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_i_308_, v___x_321_);
v_i_308_ = v___x_322_;
v_b_310_ = v_a_320_;
goto _start;
}
else
{
return v___y_319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(uint8_t v_pu_333_, uint8_t v_pu_334_, lean_object* v_c_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_333_, v_c_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_396_; 
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_343_, 0);
lean_dec(v_unused_397_);
v___x_345_ = v___x_343_;
v_isShared_346_ = v_isSharedCheck_396_;
goto v_resetjp_344_;
}
else
{
lean_dec(v___x_343_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_396_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
switch(lean_obj_tag(v_c_335_))
{
case 0:
{
lean_object* v_k_347_; 
lean_del_object(v___x_345_);
v_k_347_ = lean_ctor_get(v_c_335_, 1);
v_c_335_ = v_k_347_;
goto _start;
}
case 1:
{
lean_object* v_decl_349_; lean_object* v_k_350_; lean_object* v_value_351_; lean_object* v___x_352_; 
lean_del_object(v___x_345_);
v_decl_349_ = lean_ctor_get(v_c_335_, 0);
v_k_350_ = lean_ctor_get(v_c_335_, 1);
v_value_351_ = lean_ctor_get(v_decl_349_, 4);
v___x_352_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_333_, v_pu_334_, v_value_351_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_dec_ref(v___x_352_);
v_c_335_ = v_k_350_;
goto _start;
}
else
{
return v___x_352_;
}
}
case 2:
{
lean_object* v_decl_354_; lean_object* v_k_355_; lean_object* v_value_356_; lean_object* v___x_357_; 
lean_del_object(v___x_345_);
v_decl_354_ = lean_ctor_get(v_c_335_, 0);
v_k_355_ = lean_ctor_get(v_c_335_, 1);
v_value_356_ = lean_ctor_get(v_decl_354_, 4);
v___x_357_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_333_, v_pu_334_, v_value_356_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_dec_ref(v___x_357_);
v_c_335_ = v_k_355_;
goto _start;
}
else
{
return v___x_357_;
}
}
case 4:
{
lean_object* v_cases_359_; lean_object* v_alts_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_cases_359_ = lean_ctor_get(v_c_335_, 0);
v_alts_360_ = lean_ctor_get(v_cases_359_, 3);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_array_get_size(v_alts_360_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_nat_dec_lt(v___x_361_, v___x_362_);
if (v___x_364_ == 0)
{
lean_object* v___x_366_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_363_);
v___x_366_ = v___x_345_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
else
{
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_le(v___x_362_, v___x_362_);
if (v___x_368_ == 0)
{
if (v___x_364_ == 0)
{
lean_object* v___x_370_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_363_);
v___x_370_ = v___x_345_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_363_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; 
lean_del_object(v___x_345_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = lean_usize_of_nat(v___x_362_);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_333_, v_pu_334_, v_alts_360_, v___x_372_, v___x_373_, v___x_363_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
return v___x_374_;
}
}
else
{
size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
lean_del_object(v___x_345_);
v___x_375_ = ((size_t)0ULL);
v___x_376_ = lean_usize_of_nat(v___x_362_);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_333_, v_pu_334_, v_alts_360_, v___x_375_, v___x_376_, v___x_363_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
return v___x_377_;
}
}
}
case 7:
{
lean_object* v_k_378_; 
lean_del_object(v___x_345_);
v_k_378_ = lean_ctor_get(v_c_335_, 3);
v_c_335_ = v_k_378_;
goto _start;
}
case 8:
{
lean_object* v_k_380_; 
lean_del_object(v___x_345_);
v_k_380_ = lean_ctor_get(v_c_335_, 3);
v_c_335_ = v_k_380_;
goto _start;
}
case 9:
{
lean_object* v_k_382_; 
lean_del_object(v___x_345_);
v_k_382_ = lean_ctor_get(v_c_335_, 5);
v_c_335_ = v_k_382_;
goto _start;
}
case 10:
{
lean_object* v_k_384_; 
lean_del_object(v___x_345_);
v_k_384_ = lean_ctor_get(v_c_335_, 2);
v_c_335_ = v_k_384_;
goto _start;
}
case 11:
{
lean_object* v_k_386_; 
lean_del_object(v___x_345_);
v_k_386_ = lean_ctor_get(v_c_335_, 2);
v_c_335_ = v_k_386_;
goto _start;
}
case 12:
{
lean_object* v_k_388_; 
lean_del_object(v___x_345_);
v_k_388_ = lean_ctor_get(v_c_335_, 2);
v_c_335_ = v_k_388_;
goto _start;
}
case 13:
{
lean_object* v_k_390_; 
lean_del_object(v___x_345_);
v_k_390_ = lean_ctor_get(v_c_335_, 1);
v_c_335_ = v_k_390_;
goto _start;
}
default: 
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_box(0);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_392_);
v___x_394_ = v___x_345_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
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
}
else
{
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t v_pu_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_398_, v_pu_398_, v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object* v_pu_408_, lean_object* v_declName_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_pu_boxed_417_; lean_object* v_res_418_; 
v_pu_boxed_417_ = lean_unbox(v_pu_408_);
v_res_418_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_boxed_417_, v_declName_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_declName_409_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object* v_pu_419_, lean_object* v_code_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
uint8_t v_pu_boxed_428_; lean_object* v_res_429_; 
v_pu_boxed_428_ = lean_unbox(v_pu_419_);
v_res_429_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_boxed_428_, v_code_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec_ref(v_code_420_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object* v_pu_430_, lean_object* v_pu_431_, lean_object* v_as_432_, lean_object* v_i_433_, lean_object* v_stop_434_, lean_object* v_b_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v_pu_boxed_443_; uint8_t v_pu_boxed_444_; size_t v_i_boxed_445_; size_t v_stop_boxed_446_; lean_object* v_res_447_; 
v_pu_boxed_443_ = lean_unbox(v_pu_430_);
v_pu_boxed_444_ = lean_unbox(v_pu_431_);
v_i_boxed_445_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_stop_boxed_446_ = lean_unbox_usize(v_stop_434_);
lean_dec(v_stop_434_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_443_, v_pu_boxed_444_, v_as_432_, v_i_boxed_445_, v_stop_boxed_446_, v_b_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v_as_432_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object* v_pu_448_, lean_object* v_decl_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
uint8_t v_pu_boxed_457_; lean_object* v_res_458_; 
v_pu_boxed_457_ = lean_unbox(v_pu_448_);
v_res_458_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_boxed_457_, v_decl_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object* v_pu_459_, lean_object* v_pu_460_, lean_object* v_c_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v_pu_boxed_469_; uint8_t v_pu_boxed_470_; lean_object* v_res_471_; 
v_pu_boxed_469_ = lean_unbox(v_pu_459_);
v_pu_boxed_470_ = lean_unbox(v_pu_460_);
v_res_471_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_469_, v_pu_boxed_470_, v_c_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec_ref(v_c_461_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(uint8_t v_pu_472_, lean_object* v_f_473_, lean_object* v_v_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_473_, v_v_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object* v_pu_483_, lean_object* v_f_484_, lean_object* v_v_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v_pu_boxed_493_; lean_object* v_res_494_; 
v_pu_boxed_493_ = lean_unbox(v_pu_483_);
v_res_494_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_boxed_493_, v_f_484_, v_v_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object* v_00_u03b2_495_, lean_object* v_m_496_, lean_object* v_a_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_496_, v_a_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object* v_00_u03b2_499_, lean_object* v_m_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_499_, v_m_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_m_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(lean_object* v_00_u03b2_504_, lean_object* v_m_505_, lean_object* v_a_506_, lean_object* v_b_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_m_505_, v_a_506_, v_b_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_510_, v_a_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(lean_object* v_00_u03b2_513_, lean_object* v_m_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(v_00_u03b2_513_, v_m_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_m_514_);
return v_res_516_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_521_, v_a_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec(v_a_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(lean_object* v_00_u03b2_526_, lean_object* v_data_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_data_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(v_00_u03b2_533_, v_a_534_, v_x_535_);
lean_dec(v_x_535_);
lean_dec(v_a_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_537_, lean_object* v_i_538_, lean_object* v_source_539_, lean_object* v_target_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v_i_538_, v_source_539_, v_target_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t v_pu_546_, lean_object* v_as_547_, size_t v_i_548_, size_t v_stop_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_eq(v_i_548_, v_stop_549_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_array_uget_borrowed(v_as_547_, v_i_548_);
lean_inc(v___x_559_);
v___x_560_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_546_, v___x_559_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; size_t v___x_562_; size_t v___x_563_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v___x_560_);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_548_, v___x_562_);
v_i_548_ = v___x_563_;
v_b_550_ = v_a_561_;
goto _start;
}
else
{
return v___x_560_;
}
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_b_550_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object* v_pu_566_, lean_object* v_as_567_, lean_object* v_i_568_, lean_object* v_stop_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v_pu_boxed_578_; size_t v_i_boxed_579_; size_t v_stop_boxed_580_; lean_object* v_res_581_; 
v_pu_boxed_578_ = lean_unbox(v_pu_566_);
v_i_boxed_579_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_stop_boxed_580_ = lean_unbox_usize(v_stop_569_);
lean_dec(v_stop_569_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_578_, v_as_567_, v_i_boxed_579_, v_stop_boxed_580_, v_b_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_as_567_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t v_pu_582_, lean_object* v_decls_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v_decls_583_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
return v___x_595_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = lean_nat_dec_le(v___x_592_, v___x_592_);
if (v___x_596_ == 0)
{
if (v___x_594_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_593_);
return v___x_597_;
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
v___x_598_ = ((size_t)0ULL);
v___x_599_ = lean_usize_of_nat(v___x_592_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_582_, v_decls_583_, v___x_598_, v___x_599_, v___x_593_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_600_;
}
}
else
{
size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_592_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_582_, v_decls_583_, v___x_601_, v___x_602_, v___x_593_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object* v_pu_604_, lean_object* v_decls_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
uint8_t v_pu_boxed_613_; lean_object* v_res_614_; 
v_pu_boxed_613_ = lean_unbox(v_pu_604_);
v_res_614_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_boxed_613_, v_decls_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec_ref(v_decls_605_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t v_sz_615_, size_t v_i_616_, lean_object* v_bs_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_616_, v_sz_615_);
if (v___x_618_ == 0)
{
return v_bs_617_;
}
else
{
lean_object* v_v_619_; lean_object* v_toSignature_620_; lean_object* v_name_621_; lean_object* v___x_622_; lean_object* v_bs_x27_623_; lean_object* v___x_624_; size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
v_v_619_ = lean_array_uget(v_bs_617_, v_i_616_);
v_toSignature_620_ = lean_ctor_get(v_v_619_, 0);
v_name_621_ = lean_ctor_get(v_toSignature_620_, 0);
lean_inc(v_name_621_);
v___x_622_ = lean_unsigned_to_nat(0u);
v_bs_x27_623_ = lean_array_uset(v_bs_617_, v_i_616_, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_name_621_);
lean_ctor_set(v___x_624_, 1, v_v_619_);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_616_, v___x_625_);
v___x_627_ = lean_array_uset(v_bs_x27_623_, v_i_616_, v___x_624_);
v_i_616_ = v___x_626_;
v_bs_617_ = v___x_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object* v_sz_629_, lean_object* v_i_630_, lean_object* v_bs_631_){
_start:
{
size_t v_sz_boxed_632_; size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_sz_boxed_632_ = lean_unbox_usize(v_sz_629_);
lean_dec(v_sz_629_);
v_i_boxed_633_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_632_, v_i_boxed_633_, v_bs_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_dec(v_b_636_);
lean_dec(v_a_635_);
return v_x_637_;
}
else
{
lean_object* v_key_638_; lean_object* v_value_639_; lean_object* v_tail_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_652_; 
v_key_638_ = lean_ctor_get(v_x_637_, 0);
v_value_639_ = lean_ctor_get(v_x_637_, 1);
v_tail_640_ = lean_ctor_get(v_x_637_, 2);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_652_ == 0)
{
v___x_642_ = v_x_637_;
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_tail_640_);
lean_inc(v_value_639_);
lean_inc(v_key_638_);
lean_dec(v_x_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
uint8_t v___x_644_; 
v___x_644_ = lean_name_eq(v_key_638_, v_a_635_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_635_, v_b_636_, v_tail_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 2, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_key_638_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_value_639_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v_value_639_);
lean_dec(v_key_638_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_b_636_);
lean_ctor_set(v___x_642_, 0, v_a_635_);
v___x_650_ = v___x_642_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_635_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_b_636_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_tail_640_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(lean_object* v_m_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
lean_object* v_size_656_; lean_object* v_buckets_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_703_; 
v_size_656_ = lean_ctor_get(v_m_653_, 0);
v_buckets_657_ = lean_ctor_get(v_m_653_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_m_653_);
if (v_isSharedCheck_703_ == 0)
{
v___x_659_ = v_m_653_;
v_isShared_660_ = v_isSharedCheck_703_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_buckets_657_);
lean_inc(v_size_656_);
lean_dec(v_m_653_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_703_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; uint64_t v___y_663_; 
v___x_661_ = lean_array_get_size(v_buckets_657_);
if (lean_obj_tag(v_a_654_) == 0)
{
uint64_t v___x_701_; 
v___x_701_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_663_ = v___x_701_;
goto v___jp_662_;
}
else
{
uint64_t v_hash_702_; 
v_hash_702_ = lean_ctor_get_uint64(v_a_654_, sizeof(void*)*2);
v___y_663_ = v_hash_702_;
goto v___jp_662_;
}
v___jp_662_:
{
uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v_fold_666_; uint64_t v___x_667_; uint64_t v___x_668_; uint64_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v_bkt_675_; uint8_t v___x_676_; 
v___x_664_ = 32ULL;
v___x_665_ = lean_uint64_shift_right(v___y_663_, v___x_664_);
v_fold_666_ = lean_uint64_xor(v___y_663_, v___x_665_);
v___x_667_ = 16ULL;
v___x_668_ = lean_uint64_shift_right(v_fold_666_, v___x_667_);
v___x_669_ = lean_uint64_xor(v_fold_666_, v___x_668_);
v___x_670_ = lean_uint64_to_usize(v___x_669_);
v___x_671_ = lean_usize_of_nat(v___x_661_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_sub(v___x_671_, v___x_672_);
v___x_674_ = lean_usize_land(v___x_670_, v___x_673_);
v_bkt_675_ = lean_array_uget_borrowed(v_buckets_657_, v___x_674_);
v___x_676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_654_, v_bkt_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v_size_x27_678_; lean_object* v___x_679_; lean_object* v_buckets_x27_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_677_ = lean_unsigned_to_nat(1u);
v_size_x27_678_ = lean_nat_add(v_size_656_, v___x_677_);
lean_dec(v_size_656_);
lean_inc(v_bkt_675_);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v_a_654_);
lean_ctor_set(v___x_679_, 1, v_b_655_);
lean_ctor_set(v___x_679_, 2, v_bkt_675_);
v_buckets_x27_680_ = lean_array_uset(v_buckets_657_, v___x_674_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(4u);
v___x_682_ = lean_nat_mul(v_size_x27_678_, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(3u);
v___x_684_ = lean_nat_div(v___x_682_, v___x_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_array_get_size(v_buckets_x27_680_);
v___x_686_ = lean_nat_dec_le(v___x_684_, v___x_685_);
lean_dec(v___x_684_);
if (v___x_686_ == 0)
{
lean_object* v_val_687_; lean_object* v___x_689_; 
v_val_687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_680_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v_val_687_);
lean_ctor_set(v___x_659_, 0, v_size_x27_678_);
v___x_689_ = v___x_659_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_size_x27_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_val_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
lean_object* v___x_692_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v_buckets_x27_680_);
lean_ctor_set(v___x_659_, 0, v_size_x27_678_);
v___x_692_ = v___x_659_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_size_x27_678_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_buckets_x27_680_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v___x_694_; lean_object* v_buckets_x27_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_inc(v_bkt_675_);
v___x_694_ = lean_box(0);
v_buckets_x27_695_ = lean_array_uset(v_buckets_657_, v___x_674_, v___x_694_);
v___x_696_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_654_, v_b_655_, v_bkt_675_);
v___x_697_ = lean_array_uset(v_buckets_x27_695_, v___x_674_, v___x_696_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_697_);
v___x_699_ = v___x_659_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_size_656_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(lean_object* v_as_704_, size_t v_sz_705_, size_t v_i_706_, lean_object* v_b_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_708_ == 0)
{
return v_b_707_;
}
else
{
lean_object* v_a_709_; lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v_r_712_; size_t v___x_713_; size_t v___x_714_; 
v_a_709_ = lean_array_uget_borrowed(v_as_704_, v_i_706_);
v_fst_710_ = lean_ctor_get(v_a_709_, 0);
v_snd_711_ = lean_ctor_get(v_a_709_, 1);
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
v_r_712_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_b_707_, v_fst_710_, v_snd_711_);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_add(v_i_706_, v___x_713_);
v_i_706_ = v___x_714_;
v_b_707_ = v_r_712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(lean_object* v_as_716_, lean_object* v_sz_717_, lean_object* v_i_718_, lean_object* v_b_719_){
_start:
{
size_t v_sz_boxed_720_; size_t v_i_boxed_721_; lean_object* v_res_722_; 
v_sz_boxed_720_ = lean_unbox_usize(v_sz_717_);
lean_dec(v_sz_717_);
v_i_boxed_721_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_716_, v_sz_boxed_720_, v_i_boxed_721_, v_b_719_);
lean_dec_ref(v_as_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object* v_m_723_, lean_object* v_l_724_){
_start:
{
size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_sz_725_ = lean_array_size(v_l_724_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_l_724_, v_sz_725_, v___x_726_, v_m_723_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object* v_m_728_, lean_object* v_l_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_728_, v_l_729_);
lean_dec_ref(v_l_729_);
return v_res_730_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = lean_unsigned_to_nat(16u);
v___x_733_ = lean_mk_array(v___x_732_, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t v_pu_737_, lean_object* v_decls_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; size_t v_sz_758_; size_t v___x_759_; lean_object* v___x_760_; lean_object* v_declsMap_761_; lean_object* v___x_762_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_box(0);
v___x_746_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
v___x_747_ = lean_array_get_size(v_decls_738_);
v___x_748_ = lean_unsigned_to_nat(4u);
v___x_749_ = lean_nat_mul(v___x_747_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(3u);
v___x_751_ = lean_nat_div(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
v___x_752_ = l_Nat_nextPowerOfTwo(v___x_751_);
lean_dec(v___x_751_);
v___x_753_ = lean_mk_array(v___x_752_, v___x_745_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_744_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_mk_empty_array_with_capacity(v___x_747_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_st_mk_ref(v___x_756_);
v_sz_758_ = lean_array_size(v_decls_738_);
v___x_759_ = ((size_t)0ULL);
lean_inc_ref(v_decls_738_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_758_, v___x_759_, v_decls_738_);
v_declsMap_761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_746_, v___x_760_);
lean_dec_ref(v___x_760_);
v___x_762_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_737_, v_decls_738_, v_declsMap_761_, v___x_757_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec_ref(v_declsMap_761_);
lean_dec_ref(v_decls_738_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_771_; 
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_762_, 0);
lean_dec(v_unused_772_);
v___x_764_ = v___x_762_;
v_isShared_765_ = v_isSharedCheck_771_;
goto v_resetjp_763_;
}
else
{
lean_dec(v___x_762_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_771_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v_order_767_; lean_object* v___x_769_; 
v___x_766_ = lean_st_ref_get(v___x_757_);
lean_dec(v___x_757_);
v_order_767_ = lean_ctor_get(v___x_766_, 1);
lean_inc_ref(v_order_767_);
lean_dec(v___x_766_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_order_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_order_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v___x_757_);
v_a_773_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_762_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_762_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object* v_pu_781_, lean_object* v_decls_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
uint8_t v_pu_boxed_788_; lean_object* v_res_789_; 
v_pu_boxed_788_ = lean_unbox(v_pu_781_);
v_res_789_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_boxed_788_, v_decls_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object* v_00_u03b2_790_, lean_object* v_m_791_, lean_object* v_a_792_, lean_object* v_b_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_m_791_, v_a_792_, v_b_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_b_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_796_, v_b_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t v_pu_800_, lean_object* v_decls_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_800_, v_decls_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object* v_pu_808_, lean_object* v_decls_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
uint8_t v_pu_boxed_815_; lean_object* v_res_816_; 
v_pu_boxed_815_ = lean_unbox(v_pu_808_);
v_res_816_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_boxed_815_, v_decls_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t v___x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v___x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object* v___x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_28__boxed_832_; lean_object* v_res_833_; 
v___x_28__boxed_832_ = lean_unbox(v___x_825_);
v_res_833_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_28__boxed_832_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_833_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_toposortPass___closed__2(void){
_start:
{
uint8_t v___x_837_; uint8_t v___x_838_; 
v___x_837_ = 2;
v___x_838_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__3(void){
_start:
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___f_841_; 
v___x_839_ = lean_uint8_once(&l_Lean_Compiler_LCNF_toposortPass___closed__2, &l_Lean_Compiler_LCNF_toposortPass___closed__2_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__2);
v___x_840_ = lean_box(v___x_839_);
v___f_841_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed), 7, 1);
lean_closure_set(v___f_841_, 0, v___x_840_);
return v___f_841_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__4(void){
_start:
{
lean_object* v___f_842_; lean_object* v___x_843_; uint8_t v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___f_842_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__3, &l_Lean_Compiler_LCNF_toposortPass___closed__3_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__3);
v___x_843_ = ((lean_object*)(l_Lean_Compiler_LCNF_toposortPass___closed__1));
v___x_844_ = 0;
v___x_845_ = 2;
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_843_);
lean_ctor_set(v___x_847_, 2, v___f_842_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3, v___x_845_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 1, v___x_845_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 2, v___x_844_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass(void){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__4, &l_Lean_Compiler_LCNF_toposortPass___closed__4_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__4);
return v___x_848_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
