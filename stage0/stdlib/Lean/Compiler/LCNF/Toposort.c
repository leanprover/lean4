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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_nbuckets_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_86_ = lean_array_get_size(v_data_85_);
v___x_87_ = lean_unsigned_to_nat(2u);
v_nbuckets_88_ = lean_nat_mul(v___x_86_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_box(0);
v___x_91_ = lean_mk_array(v_nbuckets_88_, v___x_90_);
v___x_92_ = lean_array_propagate_mark(v_data_85_, v___x_91_);
v___x_93_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v___x_89_, v_data_85_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object* v_m_94_, lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_size_97_; lean_object* v_buckets_98_; lean_object* v___x_99_; uint64_t v___y_101_; 
v_size_97_ = lean_ctor_get(v_m_94_, 0);
v_buckets_98_ = lean_ctor_get(v_m_94_, 1);
v___x_99_ = lean_array_get_size(v_buckets_98_);
if (lean_obj_tag(v_a_95_) == 0)
{
uint64_t v___x_138_; 
v___x_138_ = 1723ULL;
v___y_101_ = v___x_138_;
goto v___jp_100_;
}
else
{
uint64_t v_hash_139_; 
v_hash_139_ = lean_ctor_get_uint64(v_a_95_, sizeof(void*)*2);
v___y_101_ = v_hash_139_;
goto v___jp_100_;
}
v___jp_100_:
{
uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v_fold_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v_bkt_113_; uint8_t v___x_114_; 
v___x_102_ = 32ULL;
v___x_103_ = lean_uint64_shift_right(v___y_101_, v___x_102_);
v_fold_104_ = lean_uint64_xor(v___y_101_, v___x_103_);
v___x_105_ = 16ULL;
v___x_106_ = lean_uint64_shift_right(v_fold_104_, v___x_105_);
v___x_107_ = lean_uint64_xor(v_fold_104_, v___x_106_);
v___x_108_ = lean_uint64_to_usize(v___x_107_);
v___x_109_ = lean_usize_of_nat(v___x_99_);
v___x_110_ = ((size_t)1ULL);
v___x_111_ = lean_usize_sub(v___x_109_, v___x_110_);
v___x_112_ = lean_usize_land(v___x_108_, v___x_111_);
v_bkt_113_ = lean_array_uget_borrowed(v_buckets_98_, v___x_112_);
v___x_114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_95_, v_bkt_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_135_; 
lean_inc_ref(v_buckets_98_);
lean_inc(v_size_97_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_m_94_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_136_ = lean_ctor_get(v_m_94_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_m_94_, 0);
lean_dec(v_unused_137_);
v___x_116_ = v_m_94_;
v_isShared_117_ = v_isSharedCheck_135_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_m_94_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_135_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v_size_x27_119_; lean_object* v___x_120_; lean_object* v_buckets_x27_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v_size_x27_119_ = lean_nat_add(v_size_97_, v___x_118_);
lean_dec(v_size_97_);
lean_inc(v_bkt_113_);
v___x_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_120_, 0, v_a_95_);
lean_ctor_set(v___x_120_, 1, v_b_96_);
lean_ctor_set(v___x_120_, 2, v_bkt_113_);
v_buckets_x27_121_ = lean_array_uset(v_buckets_98_, v___x_112_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(4u);
v___x_123_ = lean_nat_mul(v_size_x27_119_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(3u);
v___x_125_ = lean_nat_div(v___x_123_, v___x_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_array_get_size(v_buckets_x27_121_);
v___x_127_ = lean_nat_dec_le(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v_val_128_; lean_object* v___x_130_; 
v_val_128_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_121_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_val_128_);
lean_ctor_set(v___x_116_, 0, v_size_x27_119_);
v___x_130_ = v___x_116_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_size_x27_119_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_val_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
else
{
lean_object* v___x_133_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_buckets_x27_121_);
lean_ctor_set(v___x_116_, 0, v_size_x27_119_);
v___x_133_ = v___x_116_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_size_x27_119_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_buckets_x27_121_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_dec(v_b_96_);
lean_dec(v_a_95_);
return v_m_94_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object* v_m_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_buckets_142_; lean_object* v___x_143_; uint64_t v___y_145_; 
v_buckets_142_ = lean_ctor_get(v_m_140_, 1);
v___x_143_ = lean_array_get_size(v_buckets_142_);
if (lean_obj_tag(v_a_141_) == 0)
{
uint64_t v___x_159_; 
v___x_159_ = 1723ULL;
v___y_145_ = v___x_159_;
goto v___jp_144_;
}
else
{
uint64_t v_hash_160_; 
v_hash_160_ = lean_ctor_get_uint64(v_a_141_, sizeof(void*)*2);
v___y_145_ = v_hash_160_;
goto v___jp_144_;
}
v___jp_144_:
{
uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v_fold_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_146_ = 32ULL;
v___x_147_ = lean_uint64_shift_right(v___y_145_, v___x_146_);
v_fold_148_ = lean_uint64_xor(v___y_145_, v___x_147_);
v___x_149_ = 16ULL;
v___x_150_ = lean_uint64_shift_right(v_fold_148_, v___x_149_);
v___x_151_ = lean_uint64_xor(v_fold_148_, v___x_150_);
v___x_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = lean_usize_of_nat(v___x_143_);
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_sub(v___x_153_, v___x_154_);
v___x_156_ = lean_usize_land(v___x_152_, v___x_155_);
v___x_157_ = lean_array_uget_borrowed(v_buckets_142_, v___x_156_);
v___x_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_141_, v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object* v_m_161_, lean_object* v_a_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_m_161_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_key_168_; lean_object* v_value_169_; lean_object* v_tail_170_; uint8_t v___x_171_; 
v_key_168_ = lean_ctor_get(v_x_166_, 0);
v_value_169_ = lean_ctor_get(v_x_166_, 1);
v_tail_170_ = lean_ctor_get(v_x_166_, 2);
v___x_171_ = lean_name_eq(v_key_168_, v_a_165_);
if (v___x_171_ == 0)
{
v_x_166_ = v_tail_170_;
goto _start;
}
else
{
lean_object* v___x_173_; 
lean_inc(v_value_169_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_value_169_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg___boxed(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_174_, v_x_175_);
lean_dec(v_x_175_);
lean_dec(v_a_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(lean_object* v_m_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_buckets_179_; lean_object* v___x_180_; uint64_t v___y_182_; 
v_buckets_179_ = lean_ctor_get(v_m_177_, 1);
v___x_180_ = lean_array_get_size(v_buckets_179_);
if (lean_obj_tag(v_a_178_) == 0)
{
uint64_t v___x_196_; 
v___x_196_ = 1723ULL;
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
else
{
uint64_t v_hash_197_; 
v_hash_197_ = lean_ctor_get_uint64(v_a_178_, sizeof(void*)*2);
v___y_182_ = v_hash_197_;
goto v___jp_181_;
}
v___jp_181_:
{
uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v_fold_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_183_ = 32ULL;
v___x_184_ = lean_uint64_shift_right(v___y_182_, v___x_183_);
v_fold_185_ = lean_uint64_xor(v___y_182_, v___x_184_);
v___x_186_ = 16ULL;
v___x_187_ = lean_uint64_shift_right(v_fold_185_, v___x_186_);
v___x_188_ = lean_uint64_xor(v_fold_185_, v___x_187_);
v___x_189_ = lean_uint64_to_usize(v___x_188_);
v___x_190_ = lean_usize_of_nat(v___x_180_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_sub(v___x_190_, v___x_191_);
v___x_193_ = lean_usize_land(v___x_189_, v___x_192_);
v___x_194_ = lean_array_uget_borrowed(v_buckets_179_, v___x_193_);
v___x_195_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_178_, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg___boxed(lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_m_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(lean_object* v_pu_201_, lean_object* v_x_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
uint8_t v_pu_boxed_210_; lean_object* v_res_211_; 
v_pu_boxed_210_ = lean_unbox(v_pu_201_);
v_res_211_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(v_pu_boxed_210_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec_ref(v_x_202_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(uint8_t v_pu_212_, lean_object* v_decl_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___y_222_; lean_object* v___x_237_; lean_object* v_toSignature_238_; lean_object* v_seen_239_; lean_object* v_value_240_; lean_object* v_name_241_; uint8_t v___x_242_; 
v___x_237_ = lean_st_ref_get(v_a_215_);
v_toSignature_238_ = lean_ctor_get(v_decl_213_, 0);
v_seen_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_seen_239_);
lean_dec(v___x_237_);
v_value_240_ = lean_ctor_get(v_decl_213_, 1);
v_name_241_ = lean_ctor_get(v_toSignature_238_, 0);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_seen_239_, v_name_241_);
lean_dec_ref(v_seen_239_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_seen_245_; lean_object* v_order_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_266_; 
v___x_243_ = lean_st_ref_get(v_a_219_);
v___x_244_ = lean_st_ref_take(v_a_215_);
v_seen_245_ = lean_ctor_get(v___x_244_, 0);
v_order_246_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_266_ == 0)
{
v___x_248_ = v___x_244_;
v_isShared_249_ = v_isSharedCheck_266_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_order_246_);
lean_inc(v_seen_245_);
lean_dec(v___x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_266_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_box(0);
lean_inc(v_name_241_);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_seen_245_, v_name_241_, v___x_250_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_251_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_order_246_);
v___x_253_ = v_reuseFailAlloc_265_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___f_256_; lean_object* v___x_257_; 
v___x_254_ = lean_st_ref_put(v_a_215_, v___x_253_);
v___x_255_ = lean_box(v_pu_212_);
v___f_256_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed), 9, 1);
lean_closure_set(v___f_256_, 0, v___x_255_);
lean_inc_ref(v_value_240_);
v___x_257_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___f_256_, v_value_240_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___y_259_; lean_object* v_env_262_; lean_object* v___x_263_; 
lean_dec_ref_known(v___x_257_, 1);
v_env_262_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref_n(v_env_262_, 2);
lean_dec(v___x_243_);
lean_inc(v_name_241_);
v___x_263_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_262_, v_name_241_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_264_; 
lean_inc(v_name_241_);
v___x_264_ = lean_get_init_fn_name_for(v_env_262_, v_name_241_);
v___y_259_ = v___x_264_;
goto v___jp_258_;
}
else
{
lean_dec_ref(v_env_262_);
v___y_259_ = v___x_263_;
goto v___jp_258_;
}
v___jp_258_:
{
if (lean_obj_tag(v___y_259_) == 1)
{
lean_object* v_val_260_; lean_object* v___x_261_; 
v_val_260_ = lean_ctor_get(v___y_259_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v___y_259_, 1);
v___x_261_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_212_, v_val_260_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_val_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_dec_ref_known(v___x_261_, 1);
v___y_222_ = v_a_215_;
goto v___jp_221_;
}
else
{
lean_dec_ref(v_decl_213_);
return v___x_261_;
}
}
else
{
lean_dec(v___y_259_);
v___y_222_ = v_a_215_;
goto v___jp_221_;
}
}
}
else
{
lean_dec(v___x_243_);
lean_dec_ref(v_decl_213_);
return v___x_257_;
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v_decl_213_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v_seen_224_; lean_object* v_order_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_236_; 
v___x_223_ = lean_st_ref_take(v___y_222_);
v_seen_224_ = lean_ctor_get(v___x_223_, 0);
v_order_225_ = lean_ctor_get(v___x_223_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_236_ == 0)
{
v___x_227_ = v___x_223_;
v_isShared_228_ = v_isSharedCheck_236_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_order_225_);
lean_inc(v_seen_224_);
lean_dec(v___x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_236_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_array_push(v_order_225_, v_decl_213_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_seen_224_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_st_ref_put(v___y_222_, v___x_231_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(uint8_t v_pu_269_, lean_object* v_declName_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_a_271_, v_declName_270_);
if (lean_obj_tag(v___x_278_) == 1)
{
lean_object* v_val_279_; lean_object* v___x_280_; 
v_val_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_val_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_269_, v_val_279_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(uint8_t v_pu_283_, lean_object* v_code_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
if (lean_obj_tag(v_code_284_) == 0)
{
lean_object* v_decl_292_; lean_object* v_value_293_; 
v_decl_292_ = lean_ctor_get(v_code_284_, 0);
v_value_293_ = lean_ctor_get(v_decl_292_, 3);
switch(lean_obj_tag(v_value_293_))
{
case 3:
{
lean_object* v_declName_294_; lean_object* v___x_295_; 
v_declName_294_ = lean_ctor_get(v_value_293_, 0);
v___x_295_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_283_, v_declName_294_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_295_;
}
case 9:
{
lean_object* v_fn_296_; lean_object* v___x_297_; 
v_fn_296_ = lean_ctor_get(v_value_293_, 0);
v___x_297_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_283_, v_fn_296_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_297_;
}
case 10:
{
lean_object* v_fn_298_; lean_object* v___x_299_; 
v_fn_298_ = lean_ctor_get(v_value_293_, 0);
v___x_299_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_283_, v_fn_298_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_299_;
}
default: 
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(uint8_t v_pu_304_, uint8_t v_pu_305_, lean_object* v_as_306_, size_t v_i_307_, size_t v_stop_308_, lean_object* v_b_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___y_318_; uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_eq(v_i_307_, v_stop_308_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_array_uget_borrowed(v_as_306_, v_i_307_);
switch(lean_obj_tag(v___x_324_))
{
case 0:
{
lean_object* v_code_325_; lean_object* v___x_326_; 
v_code_325_ = lean_ctor_get(v___x_324_, 2);
v___x_326_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_304_, v_pu_305_, v_code_325_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
v___y_318_ = v___x_326_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_code_327_; lean_object* v___x_328_; 
v_code_327_ = lean_ctor_get(v___x_324_, 1);
v___x_328_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_304_, v_pu_305_, v_code_327_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
v___y_318_ = v___x_328_;
goto v___jp_317_;
}
default: 
{
lean_object* v_code_329_; lean_object* v___x_330_; 
v_code_329_ = lean_ctor_get(v___x_324_, 0);
v___x_330_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_304_, v_pu_305_, v_code_329_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
v___y_318_ = v___x_330_;
goto v___jp_317_;
}
}
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_b_309_);
return v___x_331_;
}
v___jp_317_:
{
if (lean_obj_tag(v___y_318_) == 0)
{
lean_object* v_a_319_; size_t v___x_320_; size_t v___x_321_; 
v_a_319_ = lean_ctor_get(v___y_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___y_318_, 1);
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_add(v_i_307_, v___x_320_);
v_i_307_ = v___x_321_;
v_b_309_ = v_a_319_;
goto _start;
}
else
{
return v___y_318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(uint8_t v_pu_332_, uint8_t v_pu_333_, lean_object* v_c_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_332_, v_c_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_388_; 
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v___x_342_, 0);
lean_dec(v_unused_389_);
v___x_344_ = v___x_342_;
v_isShared_345_ = v_isSharedCheck_388_;
goto v_resetjp_343_;
}
else
{
lean_dec(v___x_342_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_388_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
switch(lean_obj_tag(v_c_334_))
{
case 0:
{
lean_object* v_k_346_; 
lean_del_object(v___x_344_);
v_k_346_ = lean_ctor_get(v_c_334_, 1);
v_c_334_ = v_k_346_;
goto _start;
}
case 1:
{
lean_object* v_decl_348_; lean_object* v_k_349_; lean_object* v_value_350_; lean_object* v___x_351_; 
lean_del_object(v___x_344_);
v_decl_348_ = lean_ctor_get(v_c_334_, 0);
v_k_349_ = lean_ctor_get(v_c_334_, 1);
v_value_350_ = lean_ctor_get(v_decl_348_, 4);
v___x_351_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_332_, v_pu_333_, v_value_350_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_dec_ref_known(v___x_351_, 1);
v_c_334_ = v_k_349_;
goto _start;
}
else
{
return v___x_351_;
}
}
case 2:
{
lean_object* v_decl_353_; lean_object* v_k_354_; lean_object* v_value_355_; lean_object* v___x_356_; 
lean_del_object(v___x_344_);
v_decl_353_ = lean_ctor_get(v_c_334_, 0);
v_k_354_ = lean_ctor_get(v_c_334_, 1);
v_value_355_ = lean_ctor_get(v_decl_353_, 4);
v___x_356_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_332_, v_pu_333_, v_value_355_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_dec_ref_known(v___x_356_, 1);
v_c_334_ = v_k_354_;
goto _start;
}
else
{
return v___x_356_;
}
}
case 4:
{
lean_object* v_cases_358_; lean_object* v_alts_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_cases_358_ = lean_ctor_get(v_c_334_, 0);
v_alts_359_ = lean_ctor_get(v_cases_358_, 3);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_array_get_size(v_alts_359_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_nat_dec_lt(v___x_360_, v___x_361_);
if (v___x_363_ == 0)
{
lean_object* v___x_365_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_362_);
v___x_365_ = v___x_344_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
lean_del_object(v___x_344_);
v___x_367_ = ((size_t)0ULL);
v___x_368_ = lean_usize_of_nat(v___x_361_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_332_, v_pu_333_, v_alts_359_, v___x_367_, v___x_368_, v___x_362_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_369_;
}
}
case 7:
{
lean_object* v_k_370_; 
lean_del_object(v___x_344_);
v_k_370_ = lean_ctor_get(v_c_334_, 3);
v_c_334_ = v_k_370_;
goto _start;
}
case 8:
{
lean_object* v_k_372_; 
lean_del_object(v___x_344_);
v_k_372_ = lean_ctor_get(v_c_334_, 3);
v_c_334_ = v_k_372_;
goto _start;
}
case 9:
{
lean_object* v_k_374_; 
lean_del_object(v___x_344_);
v_k_374_ = lean_ctor_get(v_c_334_, 5);
v_c_334_ = v_k_374_;
goto _start;
}
case 10:
{
lean_object* v_k_376_; 
lean_del_object(v___x_344_);
v_k_376_ = lean_ctor_get(v_c_334_, 2);
v_c_334_ = v_k_376_;
goto _start;
}
case 11:
{
lean_object* v_k_378_; 
lean_del_object(v___x_344_);
v_k_378_ = lean_ctor_get(v_c_334_, 2);
v_c_334_ = v_k_378_;
goto _start;
}
case 12:
{
lean_object* v_k_380_; 
lean_del_object(v___x_344_);
v_k_380_ = lean_ctor_get(v_c_334_, 3);
v_c_334_ = v_k_380_;
goto _start;
}
case 13:
{
lean_object* v_k_382_; 
lean_del_object(v___x_344_);
v_k_382_ = lean_ctor_get(v_c_334_, 1);
v_c_334_ = v_k_382_;
goto _start;
}
default: 
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_box(0);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_384_);
v___x_386_ = v___x_344_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
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
}
else
{
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t v_pu_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_390_, v_pu_390_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object* v_pu_400_, lean_object* v_declName_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_pu_boxed_409_; lean_object* v_res_410_; 
v_pu_boxed_409_ = lean_unbox(v_pu_400_);
v_res_410_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_boxed_409_, v_declName_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_declName_401_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object* v_pu_411_, lean_object* v_code_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
uint8_t v_pu_boxed_420_; lean_object* v_res_421_; 
v_pu_boxed_420_ = lean_unbox(v_pu_411_);
v_res_421_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_boxed_420_, v_code_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_code_412_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object* v_pu_422_, lean_object* v_pu_423_, lean_object* v_as_424_, lean_object* v_i_425_, lean_object* v_stop_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v_pu_boxed_435_; uint8_t v_pu_boxed_436_; size_t v_i_boxed_437_; size_t v_stop_boxed_438_; lean_object* v_res_439_; 
v_pu_boxed_435_ = lean_unbox(v_pu_422_);
v_pu_boxed_436_ = lean_unbox(v_pu_423_);
v_i_boxed_437_ = lean_unbox_usize(v_i_425_);
lean_dec(v_i_425_);
v_stop_boxed_438_ = lean_unbox_usize(v_stop_426_);
lean_dec(v_stop_426_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_435_, v_pu_boxed_436_, v_as_424_, v_i_boxed_437_, v_stop_boxed_438_, v_b_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v_as_424_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object* v_pu_440_, lean_object* v_pu_441_, lean_object* v_c_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v_pu_boxed_450_; uint8_t v_pu_boxed_451_; lean_object* v_res_452_; 
v_pu_boxed_450_ = lean_unbox(v_pu_440_);
v_pu_boxed_451_ = lean_unbox(v_pu_441_);
v_res_452_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_450_, v_pu_boxed_451_, v_c_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_c_442_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object* v_pu_453_, lean_object* v_decl_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
uint8_t v_pu_boxed_462_; lean_object* v_res_463_; 
v_pu_boxed_462_ = lean_unbox(v_pu_453_);
v_res_463_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_boxed_462_, v_decl_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(uint8_t v_pu_464_, lean_object* v_f_465_, lean_object* v_v_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_465_, v_v_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object* v_pu_475_, lean_object* v_f_476_, lean_object* v_v_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
uint8_t v_pu_boxed_485_; lean_object* v_res_486_; 
v_pu_boxed_485_ = lean_unbox(v_pu_475_);
v_res_486_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_boxed_485_, v_f_476_, v_v_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object* v_00_u03b2_487_, lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_488_, v_a_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object* v_00_u03b2_491_, lean_object* v_m_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_491_, v_m_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_m_492_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(lean_object* v_00_u03b2_496_, lean_object* v_m_497_, lean_object* v_a_498_, lean_object* v_b_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_m_497_, v_a_498_, v_b_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(lean_object* v_00_u03b2_501_, lean_object* v_m_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_502_, v_a_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(lean_object* v_00_u03b2_505_, lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(v_00_u03b2_505_, v_m_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_m_506_);
return v_res_508_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object* v_00_u03b2_509_, lean_object* v_a_510_, lean_object* v_x_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_510_, v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object* v_00_u03b2_513_, lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_513_, v_a_514_, v_x_515_);
lean_dec(v_x_515_);
lean_dec(v_a_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(lean_object* v_00_u03b2_518_, lean_object* v_data_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_data_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(v_00_u03b2_525_, v_a_526_, v_x_527_);
lean_dec(v_x_527_);
lean_dec(v_a_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_529_, lean_object* v_i_530_, lean_object* v_source_531_, lean_object* v_target_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v_i_530_, v_source_531_, v_target_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_x_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t v_pu_538_, lean_object* v_as_539_, size_t v_i_540_, size_t v_stop_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_eq(v_i_540_, v_stop_541_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_array_uget_borrowed(v_as_539_, v_i_540_);
lean_inc(v___x_551_);
v___x_552_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_538_, v___x_551_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; size_t v___x_554_; size_t v___x_555_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_540_, v___x_554_);
v_i_540_ = v___x_555_;
v_b_542_ = v_a_553_;
goto _start;
}
else
{
return v___x_552_;
}
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_b_542_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object* v_pu_558_, lean_object* v_as_559_, lean_object* v_i_560_, lean_object* v_stop_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
uint8_t v_pu_boxed_570_; size_t v_i_boxed_571_; size_t v_stop_boxed_572_; lean_object* v_res_573_; 
v_pu_boxed_570_ = lean_unbox(v_pu_558_);
v_i_boxed_571_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_stop_boxed_572_ = lean_unbox_usize(v_stop_561_);
lean_dec(v_stop_561_);
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_570_, v_as_559_, v_i_boxed_571_, v_stop_boxed_572_, v_b_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_as_559_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t v_pu_574_, lean_object* v_decls_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_array_get_size(v_decls_575_);
v___x_585_ = lean_box(0);
v___x_586_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
return v___x_587_;
}
else
{
uint8_t v___x_588_; 
v___x_588_ = lean_nat_dec_le(v___x_584_, v___x_584_);
if (v___x_588_ == 0)
{
if (v___x_586_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_585_);
return v___x_589_;
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((size_t)0ULL);
v___x_591_ = lean_usize_of_nat(v___x_584_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_574_, v_decls_575_, v___x_590_, v___x_591_, v___x_585_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v___x_592_;
}
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_584_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_574_, v_decls_575_, v___x_593_, v___x_594_, v___x_585_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object* v_pu_596_, lean_object* v_decls_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_pu_boxed_605_; lean_object* v_res_606_; 
v_pu_boxed_605_ = lean_unbox(v_pu_596_);
v_res_606_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_boxed_605_, v_decls_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_decls_597_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t v_sz_607_, size_t v_i_608_, lean_object* v_bs_609_){
_start:
{
uint8_t v___x_610_; 
v___x_610_ = lean_usize_dec_lt(v_i_608_, v_sz_607_);
if (v___x_610_ == 0)
{
return v_bs_609_;
}
else
{
lean_object* v_v_611_; lean_object* v_toSignature_612_; lean_object* v_name_613_; lean_object* v___x_614_; lean_object* v_bs_x27_615_; lean_object* v___x_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v_v_611_ = lean_array_uget(v_bs_609_, v_i_608_);
v_toSignature_612_ = lean_ctor_get(v_v_611_, 0);
v_name_613_ = lean_ctor_get(v_toSignature_612_, 0);
lean_inc(v_name_613_);
v___x_614_ = lean_unsigned_to_nat(0u);
v_bs_x27_615_ = lean_array_uset(v_bs_609_, v_i_608_, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_name_613_);
lean_ctor_set(v___x_616_, 1, v_v_611_);
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_608_, v___x_617_);
v___x_619_ = lean_array_uset(v_bs_x27_615_, v_i_608_, v___x_616_);
v_i_608_ = v___x_618_;
v_bs_609_ = v___x_619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object* v_sz_621_, lean_object* v_i_622_, lean_object* v_bs_623_){
_start:
{
size_t v_sz_boxed_624_; size_t v_i_boxed_625_; lean_object* v_res_626_; 
v_sz_boxed_624_ = lean_unbox_usize(v_sz_621_);
lean_dec(v_sz_621_);
v_i_boxed_625_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_624_, v_i_boxed_625_, v_bs_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(lean_object* v_a_627_, lean_object* v_b_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_dec(v_b_628_);
lean_dec(v_a_627_);
return v_x_629_;
}
else
{
lean_object* v_key_630_; lean_object* v_value_631_; lean_object* v_tail_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_644_; 
v_key_630_ = lean_ctor_get(v_x_629_, 0);
v_value_631_ = lean_ctor_get(v_x_629_, 1);
v_tail_632_ = lean_ctor_get(v_x_629_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_629_);
if (v_isSharedCheck_644_ == 0)
{
v___x_634_ = v_x_629_;
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_tail_632_);
lean_inc(v_value_631_);
lean_inc(v_key_630_);
lean_dec(v_x_629_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = lean_name_eq(v_key_630_, v_a_627_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_627_, v_b_628_, v_tail_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 2, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_key_630_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_value_631_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v___x_642_; 
lean_dec(v_value_631_);
lean_dec(v_key_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_b_628_);
lean_ctor_set(v___x_634_, 0, v_a_627_);
v___x_642_ = v___x_634_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_627_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_b_628_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_tail_632_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(lean_object* v_m_645_, lean_object* v_a_646_, lean_object* v_b_647_){
_start:
{
lean_object* v_size_648_; lean_object* v_buckets_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_695_; 
v_size_648_ = lean_ctor_get(v_m_645_, 0);
v_buckets_649_ = lean_ctor_get(v_m_645_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_m_645_);
if (v_isSharedCheck_695_ == 0)
{
v___x_651_ = v_m_645_;
v_isShared_652_ = v_isSharedCheck_695_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_buckets_649_);
lean_inc(v_size_648_);
lean_dec(v_m_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_695_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint64_t v___y_655_; 
v___x_653_ = lean_array_get_size(v_buckets_649_);
if (lean_obj_tag(v_a_646_) == 0)
{
uint64_t v___x_693_; 
v___x_693_ = 1723ULL;
v___y_655_ = v___x_693_;
goto v___jp_654_;
}
else
{
uint64_t v_hash_694_; 
v_hash_694_ = lean_ctor_get_uint64(v_a_646_, sizeof(void*)*2);
v___y_655_ = v_hash_694_;
goto v___jp_654_;
}
v___jp_654_:
{
uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v_fold_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v_bkt_667_; uint8_t v___x_668_; 
v___x_656_ = 32ULL;
v___x_657_ = lean_uint64_shift_right(v___y_655_, v___x_656_);
v_fold_658_ = lean_uint64_xor(v___y_655_, v___x_657_);
v___x_659_ = 16ULL;
v___x_660_ = lean_uint64_shift_right(v_fold_658_, v___x_659_);
v___x_661_ = lean_uint64_xor(v_fold_658_, v___x_660_);
v___x_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = lean_usize_of_nat(v___x_653_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_sub(v___x_663_, v___x_664_);
v___x_666_ = lean_usize_land(v___x_662_, v___x_665_);
v_bkt_667_ = lean_array_uget_borrowed(v_buckets_649_, v___x_666_);
v___x_668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_646_, v_bkt_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v_size_x27_670_; lean_object* v___x_671_; lean_object* v_buckets_x27_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v_size_x27_670_ = lean_nat_add(v_size_648_, v___x_669_);
lean_dec(v_size_648_);
lean_inc(v_bkt_667_);
v___x_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_671_, 0, v_a_646_);
lean_ctor_set(v___x_671_, 1, v_b_647_);
lean_ctor_set(v___x_671_, 2, v_bkt_667_);
v_buckets_x27_672_ = lean_array_uset(v_buckets_649_, v___x_666_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(4u);
v___x_674_ = lean_nat_mul(v_size_x27_670_, v___x_673_);
v___x_675_ = lean_unsigned_to_nat(3u);
v___x_676_ = lean_nat_div(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_array_get_size(v_buckets_x27_672_);
v___x_678_ = lean_nat_dec_le(v___x_676_, v___x_677_);
lean_dec(v___x_676_);
if (v___x_678_ == 0)
{
lean_object* v_val_679_; lean_object* v___x_681_; 
v_val_679_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_672_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_val_679_);
lean_ctor_set(v___x_651_, 0, v_size_x27_670_);
v___x_681_ = v___x_651_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_x27_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_val_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v___x_684_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_buckets_x27_672_);
lean_ctor_set(v___x_651_, 0, v_size_x27_670_);
v___x_684_ = v___x_651_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_size_x27_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_buckets_x27_672_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
lean_object* v___x_686_; lean_object* v_buckets_x27_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_inc(v_bkt_667_);
v___x_686_ = lean_box(0);
v_buckets_x27_687_ = lean_array_uset(v_buckets_649_, v___x_666_, v___x_686_);
v___x_688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_646_, v_b_647_, v_bkt_667_);
v___x_689_ = lean_array_uset(v_buckets_x27_687_, v___x_666_, v___x_688_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_689_);
v___x_691_ = v___x_651_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_size_648_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(lean_object* v_as_696_, size_t v_sz_697_, size_t v_i_698_, lean_object* v_b_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_700_ == 0)
{
return v_b_699_;
}
else
{
lean_object* v_a_701_; lean_object* v_fst_702_; lean_object* v_snd_703_; lean_object* v_r_704_; size_t v___x_705_; size_t v___x_706_; 
v_a_701_ = lean_array_uget_borrowed(v_as_696_, v_i_698_);
v_fst_702_ = lean_ctor_get(v_a_701_, 0);
v_snd_703_ = lean_ctor_get(v_a_701_, 1);
lean_inc(v_snd_703_);
lean_inc(v_fst_702_);
v_r_704_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_b_699_, v_fst_702_, v_snd_703_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_698_, v___x_705_);
v_i_698_ = v___x_706_;
v_b_699_ = v_r_704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(lean_object* v_as_708_, lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_b_711_){
_start:
{
size_t v_sz_boxed_712_; size_t v_i_boxed_713_; lean_object* v_res_714_; 
v_sz_boxed_712_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_713_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_708_, v_sz_boxed_712_, v_i_boxed_713_, v_b_711_);
lean_dec_ref(v_as_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object* v_m_715_, lean_object* v_l_716_){
_start:
{
size_t v_sz_717_; size_t v___x_718_; lean_object* v___x_719_; 
v_sz_717_ = lean_array_size(v_l_716_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_l_716_, v_sz_717_, v___x_718_, v_m_715_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object* v_m_720_, lean_object* v_l_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_720_, v_l_721_);
lean_dec_ref(v_l_721_);
return v_res_722_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_box(0);
v___x_724_ = lean_unsigned_to_nat(16u);
v___x_725_ = lean_mk_array(v___x_724_, v___x_723_);
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t v_pu_729_, lean_object* v_decls_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; lean_object* v_declsMap_753_; lean_object* v___x_754_; 
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_box(0);
v___x_738_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
v___x_739_ = lean_array_get_size(v_decls_730_);
v___x_740_ = lean_unsigned_to_nat(4u);
v___x_741_ = lean_nat_mul(v___x_739_, v___x_740_);
v___x_742_ = lean_unsigned_to_nat(3u);
v___x_743_ = lean_nat_div(v___x_741_, v___x_742_);
lean_dec(v___x_741_);
v___x_744_ = l_Nat_nextPowerOfTwo(v___x_743_);
lean_dec(v___x_743_);
v___x_745_ = lean_mk_array(v___x_744_, v___x_737_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_736_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_739_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_st_mk_ref(v___x_748_);
v_sz_750_ = lean_array_size(v_decls_730_);
v___x_751_ = ((size_t)0ULL);
lean_inc_ref(v_decls_730_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_750_, v___x_751_, v_decls_730_);
v_declsMap_753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_738_, v___x_752_);
lean_dec_ref(v___x_752_);
v___x_754_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_729_, v_decls_730_, v_declsMap_753_, v___x_749_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec_ref(v_declsMap_753_);
lean_dec_ref(v_decls_730_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_763_; 
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_754_, 0);
lean_dec(v_unused_764_);
v___x_756_ = v___x_754_;
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
else
{
lean_dec(v___x_754_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v_order_759_; lean_object* v___x_761_; 
v___x_758_ = lean_st_ref_get(v___x_749_);
lean_dec(v___x_749_);
v_order_759_ = lean_ctor_get(v___x_758_, 1);
lean_inc_ref(v_order_759_);
lean_dec(v___x_758_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_order_759_);
v___x_761_ = v___x_756_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_order_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v___x_749_);
v_a_765_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_754_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_754_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object* v_pu_773_, lean_object* v_decls_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_pu_boxed_780_; lean_object* v_res_781_; 
v_pu_boxed_780_ = lean_unbox(v_pu_773_);
v_res_781_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_boxed_780_, v_decls_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object* v_00_u03b2_782_, lean_object* v_m_783_, lean_object* v_a_784_, lean_object* v_b_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_m_783_, v_a_784_, v_b_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_787_, lean_object* v_a_788_, lean_object* v_b_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_788_, v_b_789_, v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t v_pu_792_, lean_object* v_decls_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_792_, v_decls_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object* v_pu_800_, lean_object* v_decls_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
uint8_t v_pu_boxed_807_; lean_object* v_res_808_; 
v_pu_boxed_807_ = lean_unbox(v_pu_800_);
v_res_808_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_boxed_807_, v_decls_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t v___x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v___x_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object* v___x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v___x_28__boxed_824_; lean_object* v_res_825_; 
v___x_28__boxed_824_ = lean_unbox(v___x_817_);
v_res_825_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_28__boxed_824_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_825_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_toposortPass___closed__2(void){
_start:
{
uint8_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = 2;
v___x_830_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__3(void){
_start:
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___f_833_; 
v___x_831_ = lean_uint8_once(&l_Lean_Compiler_LCNF_toposortPass___closed__2, &l_Lean_Compiler_LCNF_toposortPass___closed__2_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__2);
v___x_832_ = lean_box(v___x_831_);
v___f_833_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed), 7, 1);
lean_closure_set(v___f_833_, 0, v___x_832_);
return v___f_833_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__4(void){
_start:
{
lean_object* v___f_834_; lean_object* v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___f_834_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__3, &l_Lean_Compiler_LCNF_toposortPass___closed__3_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__3);
v___x_835_ = ((lean_object*)(l_Lean_Compiler_LCNF_toposortPass___closed__1));
v___x_836_ = 0;
v___x_837_ = 2;
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_835_);
lean_ctor_set(v___x_839_, 2, v___f_834_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*3, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*3 + 1, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*3 + 2, v___x_836_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass(void){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__4, &l_Lean_Compiler_LCNF_toposortPass___closed__4_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__4);
return v___x_840_;
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
