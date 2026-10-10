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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_getInitFnNameFor_x3f(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(lean_object* v_f_1_, lean_object* v_v_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_v_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_1_, v_v_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg___boxed(lean_object* v_f_22_, lean_object* v_v_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_22_, v_v_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
return v_res_31_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(lean_object* v_a_32_, lean_object* v_x_33_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
uint8_t v___x_34_; 
v___x_34_ = 0;
return v___x_34_;
}
else
{
lean_object* v_key_35_; lean_object* v_tail_36_; uint8_t v___x_37_; 
v_key_35_ = lean_ctor_get(v_x_33_, 0);
v_tail_36_ = lean_ctor_get(v_x_33_, 2);
v___x_37_ = lean_name_eq(v_key_35_, v_a_32_);
if (v___x_37_ == 0)
{
v_x_33_ = v_tail_36_;
goto _start;
}
else
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_32_ = stack[0].m_obj;
lean_object* v_x_33_ = stack[1].m_obj;
uint8_t v_res_39_;
v_res_39_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_32_, v_x_33_);
stack->m_num = v_res_39_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg___boxed(lean_object* v_a_40_, lean_object* v_x_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_40_, v_x_41_);
lean_dec(v_x_41_);
lean_dec(v_a_40_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
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
v___x_72_ = 1723ULL;
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
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_nbuckets_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_88_ = lean_array_get_size(v_data_87_);
v___x_89_ = lean_unsigned_to_nat(2u);
v_nbuckets_90_ = lean_nat_mul(v___x_88_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_box(0);
v___x_93_ = lean_mk_array(v_nbuckets_90_, v___x_92_);
v___x_94_ = lean_array_propagate_mark(v_data_87_, v___x_93_);
v___x_95_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v___x_91_, v_data_87_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object* v_m_96_, lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_size_99_; lean_object* v_buckets_100_; lean_object* v___x_101_; uint64_t v___y_103_; 
v_size_99_ = lean_ctor_get(v_m_96_, 0);
v_buckets_100_ = lean_ctor_get(v_m_96_, 1);
v___x_101_ = lean_array_get_size(v_buckets_100_);
if (lean_obj_tag(v_a_97_) == 0)
{
uint64_t v___x_140_; 
v___x_140_ = 1723ULL;
v___y_103_ = v___x_140_;
goto v___jp_102_;
}
else
{
uint64_t v_hash_141_; 
v_hash_141_ = lean_ctor_get_uint64(v_a_97_, sizeof(void*)*2);
v___y_103_ = v_hash_141_;
goto v___jp_102_;
}
v___jp_102_:
{
uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v_fold_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v_bkt_115_; uint8_t v___x_116_; 
v___x_104_ = 32ULL;
v___x_105_ = lean_uint64_shift_right(v___y_103_, v___x_104_);
v_fold_106_ = lean_uint64_xor(v___y_103_, v___x_105_);
v___x_107_ = 16ULL;
v___x_108_ = lean_uint64_shift_right(v_fold_106_, v___x_107_);
v___x_109_ = lean_uint64_xor(v_fold_106_, v___x_108_);
v___x_110_ = lean_uint64_to_usize(v___x_109_);
v___x_111_ = lean_usize_of_nat(v___x_101_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_sub(v___x_111_, v___x_112_);
v___x_114_ = lean_usize_land(v___x_110_, v___x_113_);
v_bkt_115_ = lean_array_uget_borrowed(v_buckets_100_, v___x_114_);
v___x_116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_97_, v_bkt_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_137_; 
lean_inc_ref(v_buckets_100_);
lean_inc(v_size_99_);
v_isSharedCheck_137_ = !lean_is_exclusive(v_m_96_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; lean_object* v_unused_139_; 
v_unused_138_ = lean_ctor_get(v_m_96_, 1);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_m_96_, 0);
lean_dec(v_unused_139_);
v___x_118_ = v_m_96_;
v_isShared_119_ = v_isSharedCheck_137_;
goto v_resetjp_117_;
}
else
{
lean_dec(v_m_96_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_137_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v_size_x27_121_; lean_object* v___x_122_; lean_object* v_buckets_x27_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v_size_x27_121_ = lean_nat_add(v_size_99_, v___x_120_);
lean_dec(v_size_99_);
lean_inc(v_bkt_115_);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v_a_97_);
lean_ctor_set(v___x_122_, 1, v_b_98_);
lean_ctor_set(v___x_122_, 2, v_bkt_115_);
v_buckets_x27_123_ = lean_array_uset(v_buckets_100_, v___x_114_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(4u);
v___x_125_ = lean_nat_mul(v_size_x27_121_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(3u);
v___x_127_ = lean_nat_div(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_array_get_size(v_buckets_x27_123_);
v___x_129_ = lean_nat_dec_le(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v_val_130_; lean_object* v___x_132_; 
v_val_130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_123_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_val_130_);
lean_ctor_set(v___x_118_, 0, v_size_x27_121_);
v___x_132_ = v___x_118_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_val_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_135_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_buckets_x27_123_);
lean_ctor_set(v___x_118_, 0, v_size_x27_121_);
v___x_135_ = v___x_118_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_buckets_x27_123_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_dec(v_b_98_);
lean_dec(v_a_97_);
return v_m_96_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object* v_m_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_buckets_144_; lean_object* v___x_145_; uint64_t v___y_147_; 
v_buckets_144_ = lean_ctor_get(v_m_142_, 1);
v___x_145_ = lean_array_get_size(v_buckets_144_);
if (lean_obj_tag(v_a_143_) == 0)
{
uint64_t v___x_161_; 
v___x_161_ = 1723ULL;
v___y_147_ = v___x_161_;
goto v___jp_146_;
}
else
{
uint64_t v_hash_162_; 
v_hash_162_ = lean_ctor_get_uint64(v_a_143_, sizeof(void*)*2);
v___y_147_ = v_hash_162_;
goto v___jp_146_;
}
v___jp_146_:
{
uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v_fold_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_148_ = 32ULL;
v___x_149_ = lean_uint64_shift_right(v___y_147_, v___x_148_);
v_fold_150_ = lean_uint64_xor(v___y_147_, v___x_149_);
v___x_151_ = 16ULL;
v___x_152_ = lean_uint64_shift_right(v_fold_150_, v___x_151_);
v___x_153_ = lean_uint64_xor(v_fold_150_, v___x_152_);
v___x_154_ = lean_uint64_to_usize(v___x_153_);
v___x_155_ = lean_usize_of_nat(v___x_145_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_sub(v___x_155_, v___x_156_);
v___x_158_ = lean_usize_land(v___x_154_, v___x_157_);
v___x_159_ = lean_array_uget_borrowed(v_buckets_144_, v___x_158_);
v___x_160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_143_, v___x_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_142_ = stack[0].m_obj;
lean_object* v_a_143_ = stack[1].m_obj;
uint8_t v_res_163_;
v_res_163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_142_, v_a_143_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object* v_m_164_, lean_object* v_a_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_m_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(lean_object* v_a_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v_key_171_; lean_object* v_value_172_; lean_object* v_tail_173_; uint8_t v___x_174_; 
v_key_171_ = lean_ctor_get(v_x_169_, 0);
v_value_172_ = lean_ctor_get(v_x_169_, 1);
v_tail_173_ = lean_ctor_get(v_x_169_, 2);
v___x_174_ = lean_name_eq(v_key_171_, v_a_168_);
if (v___x_174_ == 0)
{
v_x_169_ = v_tail_173_;
goto _start;
}
else
{
lean_object* v___x_176_; 
lean_inc(v_value_172_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_value_172_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg___boxed(lean_object* v_a_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_177_, v_x_178_);
lean_dec(v_x_178_);
lean_dec(v_a_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(lean_object* v_m_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_buckets_182_; lean_object* v___x_183_; uint64_t v___y_185_; 
v_buckets_182_ = lean_ctor_get(v_m_180_, 1);
v___x_183_ = lean_array_get_size(v_buckets_182_);
if (lean_obj_tag(v_a_181_) == 0)
{
uint64_t v___x_199_; 
v___x_199_ = 1723ULL;
v___y_185_ = v___x_199_;
goto v___jp_184_;
}
else
{
uint64_t v_hash_200_; 
v_hash_200_ = lean_ctor_get_uint64(v_a_181_, sizeof(void*)*2);
v___y_185_ = v_hash_200_;
goto v___jp_184_;
}
v___jp_184_:
{
uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v_fold_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_186_ = 32ULL;
v___x_187_ = lean_uint64_shift_right(v___y_185_, v___x_186_);
v_fold_188_ = lean_uint64_xor(v___y_185_, v___x_187_);
v___x_189_ = 16ULL;
v___x_190_ = lean_uint64_shift_right(v_fold_188_, v___x_189_);
v___x_191_ = lean_uint64_xor(v_fold_188_, v___x_190_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = lean_usize_of_nat(v___x_183_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v___x_193_, v___x_194_);
v___x_196_ = lean_usize_land(v___x_192_, v___x_195_);
v___x_197_ = lean_array_uget_borrowed(v_buckets_182_, v___x_196_);
v___x_198_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_181_, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg___boxed(lean_object* v_m_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_m_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(lean_object* v_pu_204_, lean_object* v_x_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
uint8_t v_pu_boxed_213_; lean_object* v_res_214_; 
v_pu_boxed_213_ = lean_unbox(v_pu_204_);
v_res_214_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(v_pu_boxed_213_, v_x_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec_ref(v_x_205_);
return v_res_214_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(uint8_t v_pu_215_, lean_object* v_decl_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___y_225_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v_toSignature_243_; lean_object* v_seen_244_; lean_object* v_value_245_; lean_object* v_name_246_; uint8_t v___x_247_; 
v___x_240_ = lean_box(v_pu_215_);
v___f_241_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed), 9, 1);
lean_closure_set(v___f_241_, 0, v___x_240_);
v___x_242_ = lean_st_ref_get(v_a_218_);
v_toSignature_243_ = lean_ctor_get(v_decl_216_, 0);
v_seen_244_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_seen_244_);
lean_dec(v___x_242_);
v_value_245_ = lean_ctor_get(v_decl_216_, 1);
v_name_246_ = lean_ctor_get(v_toSignature_243_, 0);
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_seen_244_, v_name_246_);
lean_dec_ref(v_seen_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v_env_249_; lean_object* v___x_250_; lean_object* v_seen_251_; lean_object* v_order_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_269_; 
v___x_248_ = lean_st_ref_get(v_a_222_);
v_env_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_env_249_);
lean_dec(v___x_248_);
v___x_250_ = lean_st_ref_take(v_a_218_);
v_seen_251_ = lean_ctor_get(v___x_250_, 0);
v_order_252_ = lean_ctor_get(v___x_250_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_269_ == 0)
{
v___x_254_ = v___x_250_;
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_order_252_);
lean_inc(v_seen_251_);
lean_dec(v___x_250_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_box(0);
lean_inc(v_name_246_);
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_seen_251_, v_name_246_, v___x_256_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_order_252_);
v___x_259_ = v_reuseFailAlloc_268_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_st_ref_put(v_a_218_, v___x_259_);
lean_inc_ref(v_value_245_);
v___x_261_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___f_241_, v_value_245_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___y_263_; lean_object* v___x_266_; 
lean_dec_ref_known(v___x_261_, 1);
lean_inc(v_name_246_);
lean_inc_ref(v_env_249_);
v___x_266_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_249_, v_name_246_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; 
lean_inc(v_name_246_);
v___x_267_ = l_Lean_getInitFnNameFor_x3f(v_env_249_, v_name_246_);
v___y_263_ = v___x_267_;
goto v___jp_262_;
}
else
{
lean_dec_ref(v_env_249_);
v___y_263_ = v___x_266_;
goto v___jp_262_;
}
v___jp_262_:
{
if (lean_obj_tag(v___y_263_) == 1)
{
lean_object* v_val_264_; lean_object* v___x_265_; 
v_val_264_ = lean_ctor_get(v___y_263_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___y_263_, 1);
v___x_265_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_215_, v_val_264_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_val_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_dec_ref_known(v___x_265_, 1);
v___y_225_ = v_a_218_;
goto v___jp_224_;
}
else
{
lean_dec_ref(v_decl_216_);
return v___x_265_;
}
}
else
{
lean_dec(v___y_263_);
v___y_225_ = v_a_218_;
goto v___jp_224_;
}
}
}
else
{
lean_dec_ref(v_env_249_);
lean_dec_ref(v_decl_216_);
return v___x_261_;
}
}
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v___f_241_);
lean_dec_ref(v_decl_216_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v_seen_227_; lean_object* v_order_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_239_; 
v___x_226_ = lean_st_ref_take(v___y_225_);
v_seen_227_ = lean_ctor_get(v___x_226_, 0);
v_order_228_ = lean_ctor_get(v___x_226_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_239_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_order_228_);
lean_inc(v_seen_227_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_array_push(v_order_228_, v_decl_216_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_seen_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_238_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_st_ref_put(v___y_225_, v___x_235_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_232_);
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_215_ = stack[0].m_num;
lean_object* v_decl_216_ = stack[1].m_obj;
lean_object* v_a_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_a_219_ = stack[4].m_obj;
lean_object* v_a_220_ = stack[5].m_obj;
lean_object* v_a_221_ = stack[6].m_obj;
lean_object* v_a_222_ = stack[7].m_obj;
lean_object* v_res_272_;
v_res_272_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_215_, v_decl_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
stack->m_obj
 = v_res_272_;
}
lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(uint8_t v_pu_273_, lean_object* v_declName_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_a_275_, v_declName_274_);
if (lean_obj_tag(v___x_282_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_284_; 
v_val_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_273_, v_val_283_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_273_ = stack[0].m_num;
lean_object* v_declName_274_ = stack[1].m_obj;
lean_object* v_a_275_ = stack[2].m_obj;
lean_object* v_a_276_ = stack[3].m_obj;
lean_object* v_a_277_ = stack[4].m_obj;
lean_object* v_a_278_ = stack[5].m_obj;
lean_object* v_a_279_ = stack[6].m_obj;
lean_object* v_a_280_ = stack[7].m_obj;
lean_object* v_res_287_;
v_res_287_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_273_, v_declName_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
stack->m_obj
 = v_res_287_;
}
lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(uint8_t v_pu_288_, lean_object* v_code_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
if (lean_obj_tag(v_code_289_) == 0)
{
lean_object* v_decl_297_; lean_object* v_value_298_; 
v_decl_297_ = lean_ctor_get(v_code_289_, 0);
v_value_298_ = lean_ctor_get(v_decl_297_, 3);
switch(lean_obj_tag(v_value_298_))
{
case 3:
{
lean_object* v_declName_299_; lean_object* v___x_300_; 
v_declName_299_ = lean_ctor_get(v_value_298_, 0);
v___x_300_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_288_, v_declName_299_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_300_;
}
case 9:
{
lean_object* v_fn_301_; lean_object* v___x_302_; 
v_fn_301_ = lean_ctor_get(v_value_298_, 0);
v___x_302_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_288_, v_fn_301_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_302_;
}
case 10:
{
lean_object* v_fn_303_; lean_object* v___x_304_; 
v_fn_303_ = lean_ctor_get(v_value_298_, 0);
v___x_304_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_288_, v_fn_303_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_304_;
}
default: 
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_288_ = stack[0].m_num;
lean_object* v_code_289_ = stack[1].m_obj;
lean_object* v_a_290_ = stack[2].m_obj;
lean_object* v_a_291_ = stack[3].m_obj;
lean_object* v_a_292_ = stack[4].m_obj;
lean_object* v_a_293_ = stack[5].m_obj;
lean_object* v_a_294_ = stack[6].m_obj;
lean_object* v_a_295_ = stack[7].m_obj;
lean_object* v_res_309_;
v_res_309_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_288_, v_code_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
stack->m_obj
 = v_res_309_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(uint8_t v_pu_310_, uint8_t v_pu_311_, lean_object* v_as_312_, size_t v_i_313_, size_t v_stop_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___y_324_; uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_313_, v_stop_314_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_array_uget_borrowed(v_as_312_, v_i_313_);
switch(lean_obj_tag(v___x_330_))
{
case 0:
{
lean_object* v_code_331_; lean_object* v___x_332_; 
v_code_331_ = lean_ctor_get(v___x_330_, 2);
v___x_332_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_310_, v_pu_311_, v_code_331_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
v___y_324_ = v___x_332_;
goto v___jp_323_;
}
case 1:
{
lean_object* v_code_333_; lean_object* v___x_334_; 
v_code_333_ = lean_ctor_get(v___x_330_, 1);
v___x_334_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_310_, v_pu_311_, v_code_333_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
v___y_324_ = v___x_334_;
goto v___jp_323_;
}
default: 
{
lean_object* v_code_335_; lean_object* v___x_336_; 
v_code_335_ = lean_ctor_get(v___x_330_, 0);
v___x_336_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_310_, v_pu_311_, v_code_335_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
v___y_324_ = v___x_336_;
goto v___jp_323_;
}
}
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v_b_315_);
return v___x_337_;
}
v___jp_323_:
{
if (lean_obj_tag(v___y_324_) == 0)
{
lean_object* v_a_325_; size_t v___x_326_; size_t v___x_327_; 
v_a_325_ = lean_ctor_get(v___y_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___y_324_, 1);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_313_, v___x_326_);
v_i_313_ = v___x_327_;
v_b_315_ = v_a_325_;
goto _start;
}
else
{
return v___y_324_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_310_ = stack[0].m_num;
uint8_t v_pu_311_ = stack[1].m_num;
lean_object* v_as_312_ = stack[2].m_obj;
size_t v_i_313_ = stack[3].m_num;
size_t v_stop_314_ = stack[4].m_num;
lean_object* v_b_315_ = stack[5].m_obj;
lean_object* v___y_316_ = stack[6].m_obj;
lean_object* v___y_317_ = stack[7].m_obj;
lean_object* v___y_318_ = stack[8].m_obj;
lean_object* v___y_319_ = stack[9].m_obj;
lean_object* v___y_320_ = stack[10].m_obj;
lean_object* v___y_321_ = stack[11].m_obj;
lean_object* v_res_338_;
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_310_, v_pu_311_, v_as_312_, v_i_313_, v_stop_314_, v_b_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
stack->m_obj
 = v_res_338_;
}
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(uint8_t v_pu_339_, uint8_t v_pu_340_, lean_object* v_c_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_339_, v_c_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_395_; 
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_349_, 0);
lean_dec(v_unused_396_);
v___x_351_ = v___x_349_;
v_isShared_352_ = v_isSharedCheck_395_;
goto v_resetjp_350_;
}
else
{
lean_dec(v___x_349_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_395_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
switch(lean_obj_tag(v_c_341_))
{
case 0:
{
lean_object* v_k_353_; 
lean_del_object(v___x_351_);
v_k_353_ = lean_ctor_get(v_c_341_, 1);
v_c_341_ = v_k_353_;
goto _start;
}
case 1:
{
lean_object* v_decl_355_; lean_object* v_k_356_; lean_object* v_value_357_; lean_object* v___x_358_; 
lean_del_object(v___x_351_);
v_decl_355_ = lean_ctor_get(v_c_341_, 0);
v_k_356_ = lean_ctor_get(v_c_341_, 1);
v_value_357_ = lean_ctor_get(v_decl_355_, 4);
v___x_358_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_339_, v_pu_340_, v_value_357_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref_known(v___x_358_, 1);
v_c_341_ = v_k_356_;
goto _start;
}
else
{
return v___x_358_;
}
}
case 2:
{
lean_object* v_decl_360_; lean_object* v_k_361_; lean_object* v_value_362_; lean_object* v___x_363_; 
lean_del_object(v___x_351_);
v_decl_360_ = lean_ctor_get(v_c_341_, 0);
v_k_361_ = lean_ctor_get(v_c_341_, 1);
v_value_362_ = lean_ctor_get(v_decl_360_, 4);
v___x_363_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_339_, v_pu_340_, v_value_362_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_dec_ref_known(v___x_363_, 1);
v_c_341_ = v_k_361_;
goto _start;
}
else
{
return v___x_363_;
}
}
case 4:
{
lean_object* v_cases_365_; lean_object* v_alts_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_cases_365_ = lean_ctor_get(v_c_341_, 0);
v_alts_366_ = lean_ctor_get(v_cases_365_, 3);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_array_get_size(v_alts_366_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
if (v___x_370_ == 0)
{
lean_object* v___x_372_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_369_);
v___x_372_ = v___x_351_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_369_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
else
{
size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; 
lean_del_object(v___x_351_);
v___x_374_ = ((size_t)0ULL);
v___x_375_ = lean_usize_of_nat(v___x_368_);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_339_, v_pu_340_, v_alts_366_, v___x_374_, v___x_375_, v___x_369_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_376_;
}
}
case 7:
{
lean_object* v_k_377_; 
lean_del_object(v___x_351_);
v_k_377_ = lean_ctor_get(v_c_341_, 3);
v_c_341_ = v_k_377_;
goto _start;
}
case 8:
{
lean_object* v_k_379_; 
lean_del_object(v___x_351_);
v_k_379_ = lean_ctor_get(v_c_341_, 3);
v_c_341_ = v_k_379_;
goto _start;
}
case 9:
{
lean_object* v_k_381_; 
lean_del_object(v___x_351_);
v_k_381_ = lean_ctor_get(v_c_341_, 5);
v_c_341_ = v_k_381_;
goto _start;
}
case 10:
{
lean_object* v_k_383_; 
lean_del_object(v___x_351_);
v_k_383_ = lean_ctor_get(v_c_341_, 2);
v_c_341_ = v_k_383_;
goto _start;
}
case 11:
{
lean_object* v_k_385_; 
lean_del_object(v___x_351_);
v_k_385_ = lean_ctor_get(v_c_341_, 2);
v_c_341_ = v_k_385_;
goto _start;
}
case 12:
{
lean_object* v_k_387_; 
lean_del_object(v___x_351_);
v_k_387_ = lean_ctor_get(v_c_341_, 3);
v_c_341_ = v_k_387_;
goto _start;
}
case 13:
{
lean_object* v_k_389_; 
lean_del_object(v___x_351_);
v_k_389_ = lean_ctor_get(v_c_341_, 1);
v_c_341_ = v_k_389_;
goto _start;
}
default: 
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_391_);
v___x_393_ = v___x_351_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
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
}
else
{
return v___x_349_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_339_ = stack[0].m_num;
uint8_t v_pu_340_ = stack[1].m_num;
lean_object* v_c_341_ = stack[2].m_obj;
lean_object* v___y_342_ = stack[3].m_obj;
lean_object* v___y_343_ = stack[4].m_obj;
lean_object* v___y_344_ = stack[5].m_obj;
lean_object* v___y_345_ = stack[6].m_obj;
lean_object* v___y_346_ = stack[7].m_obj;
lean_object* v___y_347_ = stack[8].m_obj;
lean_object* v_res_397_;
v_res_397_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_339_, v_pu_340_, v_c_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
stack->m_obj
 = v_res_397_;
}
lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t v_pu_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_398_, v_pu_398_, v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_398_ = stack[0].m_num;
lean_object* v_x_399_ = stack[1].m_obj;
lean_object* v___y_400_ = stack[2].m_obj;
lean_object* v___y_401_ = stack[3].m_obj;
lean_object* v___y_402_ = stack[4].m_obj;
lean_object* v___y_403_ = stack[5].m_obj;
lean_object* v___y_404_ = stack[6].m_obj;
lean_object* v___y_405_ = stack[7].m_obj;
lean_object* v_res_408_;
v_res_408_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(v_pu_398_, v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object* v_pu_409_, lean_object* v_declName_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
uint8_t v_pu_boxed_418_; lean_object* v_res_419_; 
v_pu_boxed_418_ = lean_unbox(v_pu_409_);
v_res_419_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_boxed_418_, v_declName_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_declName_410_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object* v_pu_420_, lean_object* v_code_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
uint8_t v_pu_boxed_429_; lean_object* v_res_430_; 
v_pu_boxed_429_ = lean_unbox(v_pu_420_);
v_res_430_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_boxed_429_, v_code_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_code_421_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object* v_pu_431_, lean_object* v_pu_432_, lean_object* v_as_433_, lean_object* v_i_434_, lean_object* v_stop_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v_pu_boxed_444_; uint8_t v_pu_boxed_445_; size_t v_i_boxed_446_; size_t v_stop_boxed_447_; lean_object* v_res_448_; 
v_pu_boxed_444_ = lean_unbox(v_pu_431_);
v_pu_boxed_445_ = lean_unbox(v_pu_432_);
v_i_boxed_446_ = lean_unbox_usize(v_i_434_);
lean_dec(v_i_434_);
v_stop_boxed_447_ = lean_unbox_usize(v_stop_435_);
lean_dec(v_stop_435_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_444_, v_pu_boxed_445_, v_as_433_, v_i_boxed_446_, v_stop_boxed_447_, v_b_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v_as_433_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object* v_pu_449_, lean_object* v_pu_450_, lean_object* v_c_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_pu_boxed_459_; uint8_t v_pu_boxed_460_; lean_object* v_res_461_; 
v_pu_boxed_459_ = lean_unbox(v_pu_449_);
v_pu_boxed_460_ = lean_unbox(v_pu_450_);
v_res_461_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_459_, v_pu_boxed_460_, v_c_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_c_451_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object* v_pu_462_, lean_object* v_decl_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
uint8_t v_pu_boxed_471_; lean_object* v_res_472_; 
v_pu_boxed_471_ = lean_unbox(v_pu_462_);
v_res_472_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_boxed_471_, v_decl_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v_res_472_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(uint8_t v_pu_473_, lean_object* v_f_474_, lean_object* v_v_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_474_, v_v_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_483_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_473_ = stack[0].m_num;
lean_object* v_f_474_ = stack[1].m_obj;
lean_object* v_v_475_ = stack[2].m_obj;
lean_object* v___y_476_ = stack[3].m_obj;
lean_object* v___y_477_ = stack[4].m_obj;
lean_object* v___y_478_ = stack[5].m_obj;
lean_object* v___y_479_ = stack[6].m_obj;
lean_object* v___y_480_ = stack[7].m_obj;
lean_object* v___y_481_ = stack[8].m_obj;
lean_object* v_res_484_;
v_res_484_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_473_, v_f_474_, v_v_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
stack->m_obj
 = v_res_484_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object* v_pu_485_, lean_object* v_f_486_, lean_object* v_v_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
uint8_t v_pu_boxed_495_; lean_object* v_res_496_; 
v_pu_boxed_495_ = lean_unbox(v_pu_485_);
v_res_496_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_boxed_495_, v_f_486_, v_v_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_496_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object* v_00_u03b2_497_, lean_object* v_m_498_, lean_object* v_a_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_498_, v_a_499_);
return v___x_500_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_498_ = stack[1].m_obj;
lean_object* v_a_499_ = stack[2].m_obj;
uint8_t v_res_501_;
v_res_501_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_box(0), v_m_498_, v_a_499_);
stack->m_num = v_res_501_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object* v_00_u03b2_502_, lean_object* v_m_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_502_, v_m_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_m_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(lean_object* v_00_u03b2_507_, lean_object* v_m_508_, lean_object* v_a_509_, lean_object* v_b_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_m_508_, v_a_509_, v_b_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(lean_object* v_00_u03b2_512_, lean_object* v_m_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_513_, v_a_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(lean_object* v_00_u03b2_516_, lean_object* v_m_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(v_00_u03b2_516_, v_m_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_m_517_);
return v_res_519_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_521_ = stack[1].m_obj;
lean_object* v_x_522_ = stack[2].m_obj;
uint8_t v_res_524_;
v_res_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_box(0), v_a_521_, v_x_522_);
stack->m_num = v_res_524_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v_res_528_; lean_object* v_r_529_; 
v_res_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_525_, v_a_526_, v_x_527_);
lean_dec(v_x_527_);
lean_dec(v_a_526_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(lean_object* v_00_u03b2_530_, lean_object* v_data_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_data_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(lean_object* v_00_u03b2_537_, lean_object* v_a_538_, lean_object* v_x_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(v_00_u03b2_537_, v_a_538_, v_x_539_);
lean_dec(v_x_539_);
lean_dec(v_a_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_541_, lean_object* v_i_542_, lean_object* v_source_543_, lean_object* v_target_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v_i_542_, v_source_543_, v_target_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_x_547_, v_x_548_);
return v___x_549_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t v_pu_550_, lean_object* v_as_551_, size_t v_i_552_, size_t v_stop_553_, lean_object* v_b_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_562_; 
v___x_562_ = lean_usize_dec_eq(v_i_552_, v_stop_553_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_array_uget_borrowed(v_as_551_, v_i_552_);
lean_inc(v___x_563_);
v___x_564_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_550_, v___x_563_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; size_t v___x_566_; size_t v___x_567_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_552_, v___x_566_);
v_i_552_ = v___x_567_;
v_b_554_ = v_a_565_;
goto _start;
}
else
{
return v___x_564_;
}
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v_b_554_);
return v___x_569_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_550_ = stack[0].m_num;
lean_object* v_as_551_ = stack[1].m_obj;
size_t v_i_552_ = stack[2].m_num;
size_t v_stop_553_ = stack[3].m_num;
lean_object* v_b_554_ = stack[4].m_obj;
lean_object* v___y_555_ = stack[5].m_obj;
lean_object* v___y_556_ = stack[6].m_obj;
lean_object* v___y_557_ = stack[7].m_obj;
lean_object* v___y_558_ = stack[8].m_obj;
lean_object* v___y_559_ = stack[9].m_obj;
lean_object* v___y_560_ = stack[10].m_obj;
lean_object* v_res_570_;
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_550_, v_as_551_, v_i_552_, v_stop_553_, v_b_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object* v_pu_571_, lean_object* v_as_572_, lean_object* v_i_573_, lean_object* v_stop_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_pu_boxed_583_; size_t v_i_boxed_584_; size_t v_stop_boxed_585_; lean_object* v_res_586_; 
v_pu_boxed_583_ = lean_unbox(v_pu_571_);
v_i_boxed_584_ = lean_unbox_usize(v_i_573_);
lean_dec(v_i_573_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_574_);
lean_dec(v_stop_574_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_583_, v_as_572_, v_i_boxed_584_, v_stop_boxed_585_, v_b_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_as_572_);
return v_res_586_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t v_pu_587_, lean_object* v_decls_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_array_get_size(v_decls_588_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
return v___x_600_;
}
else
{
uint8_t v___x_601_; 
v___x_601_ = lean_nat_dec_le(v___x_597_, v___x_597_);
if (v___x_601_ == 0)
{
if (v___x_599_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_598_);
return v___x_602_;
}
else
{
size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_597_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_587_, v_decls_588_, v___x_603_, v___x_604_, v___x_598_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v___x_605_;
}
}
else
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((size_t)0ULL);
v___x_607_ = lean_usize_of_nat(v___x_597_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_587_, v_decls_588_, v___x_606_, v___x_607_, v___x_598_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_587_ = stack[0].m_num;
lean_object* v_decls_588_ = stack[1].m_obj;
lean_object* v_a_589_ = stack[2].m_obj;
lean_object* v_a_590_ = stack[3].m_obj;
lean_object* v_a_591_ = stack[4].m_obj;
lean_object* v_a_592_ = stack[5].m_obj;
lean_object* v_a_593_ = stack[6].m_obj;
lean_object* v_a_594_ = stack[7].m_obj;
lean_object* v_res_609_;
v_res_609_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_587_, v_decls_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object* v_pu_610_, lean_object* v_decls_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
uint8_t v_pu_boxed_619_; lean_object* v_res_620_; 
v_pu_boxed_619_ = lean_unbox(v_pu_610_);
v_res_620_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_boxed_619_, v_decls_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec_ref(v_decls_611_);
return v_res_620_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t v_sz_621_, size_t v_i_622_, lean_object* v_bs_623_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_lt(v_i_622_, v_sz_621_);
if (v___x_624_ == 0)
{
return v_bs_623_;
}
else
{
lean_object* v_v_625_; lean_object* v_toSignature_626_; lean_object* v_name_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; lean_object* v___x_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_v_625_ = lean_array_uget(v_bs_623_, v_i_622_);
v_toSignature_626_ = lean_ctor_get(v_v_625_, 0);
v_name_627_ = lean_ctor_get(v_toSignature_626_, 0);
lean_inc(v_name_627_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_623_, v_i_622_, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_name_627_);
lean_ctor_set(v___x_630_, 1, v_v_625_);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_622_, v___x_631_);
v___x_633_ = lean_array_uset(v_bs_x27_629_, v_i_622_, v___x_630_);
v_i_622_ = v___x_632_;
v_bs_623_ = v___x_633_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_621_ = stack[0].m_num;
size_t v_i_622_ = stack[1].m_num;
lean_object* v_bs_623_ = stack[2].m_obj;
lean_object* v_res_635_;
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_621_, v_i_622_, v_bs_623_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_bs_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_640_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_639_, v_i_boxed_640_, v_bs_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(lean_object* v_a_642_, lean_object* v_b_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_dec(v_b_643_);
lean_dec(v_a_642_);
return v_x_644_;
}
else
{
lean_object* v_key_645_; lean_object* v_value_646_; lean_object* v_tail_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_659_; 
v_key_645_ = lean_ctor_get(v_x_644_, 0);
v_value_646_ = lean_ctor_get(v_x_644_, 1);
v_tail_647_ = lean_ctor_get(v_x_644_, 2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_659_ == 0)
{
v___x_649_ = v_x_644_;
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_tail_647_);
lean_inc(v_value_646_);
lean_inc(v_key_645_);
lean_dec(v_x_644_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; 
v___x_651_ = lean_name_eq(v_key_645_, v_a_642_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_642_, v_b_643_, v_tail_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 2, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_key_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_value_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v___x_657_; 
lean_dec(v_value_646_);
lean_dec(v_key_645_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_b_643_);
lean_ctor_set(v___x_649_, 0, v_a_642_);
v___x_657_ = v___x_649_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_642_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_b_643_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_tail_647_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(lean_object* v_m_660_, lean_object* v_a_661_, lean_object* v_b_662_){
_start:
{
lean_object* v_size_663_; lean_object* v_buckets_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_710_; 
v_size_663_ = lean_ctor_get(v_m_660_, 0);
v_buckets_664_ = lean_ctor_get(v_m_660_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_m_660_);
if (v_isSharedCheck_710_ == 0)
{
v___x_666_ = v_m_660_;
v_isShared_667_ = v_isSharedCheck_710_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_buckets_664_);
lean_inc(v_size_663_);
lean_dec(v_m_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_710_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; uint64_t v___y_670_; 
v___x_668_ = lean_array_get_size(v_buckets_664_);
if (lean_obj_tag(v_a_661_) == 0)
{
uint64_t v___x_708_; 
v___x_708_ = 1723ULL;
v___y_670_ = v___x_708_;
goto v___jp_669_;
}
else
{
uint64_t v_hash_709_; 
v_hash_709_ = lean_ctor_get_uint64(v_a_661_, sizeof(void*)*2);
v___y_670_ = v_hash_709_;
goto v___jp_669_;
}
v___jp_669_:
{
uint64_t v___x_671_; uint64_t v___x_672_; uint64_t v_fold_673_; uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; size_t v___x_677_; size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v_bkt_682_; uint8_t v___x_683_; 
v___x_671_ = 32ULL;
v___x_672_ = lean_uint64_shift_right(v___y_670_, v___x_671_);
v_fold_673_ = lean_uint64_xor(v___y_670_, v___x_672_);
v___x_674_ = 16ULL;
v___x_675_ = lean_uint64_shift_right(v_fold_673_, v___x_674_);
v___x_676_ = lean_uint64_xor(v_fold_673_, v___x_675_);
v___x_677_ = lean_uint64_to_usize(v___x_676_);
v___x_678_ = lean_usize_of_nat(v___x_668_);
v___x_679_ = ((size_t)1ULL);
v___x_680_ = lean_usize_sub(v___x_678_, v___x_679_);
v___x_681_ = lean_usize_land(v___x_677_, v___x_680_);
v_bkt_682_ = lean_array_uget_borrowed(v_buckets_664_, v___x_681_);
v___x_683_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_661_, v_bkt_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v_size_x27_685_; lean_object* v___x_686_; lean_object* v_buckets_x27_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_684_ = lean_unsigned_to_nat(1u);
v_size_x27_685_ = lean_nat_add(v_size_663_, v___x_684_);
lean_dec(v_size_663_);
lean_inc(v_bkt_682_);
v___x_686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_686_, 0, v_a_661_);
lean_ctor_set(v___x_686_, 1, v_b_662_);
lean_ctor_set(v___x_686_, 2, v_bkt_682_);
v_buckets_x27_687_ = lean_array_uset(v_buckets_664_, v___x_681_, v___x_686_);
v___x_688_ = lean_unsigned_to_nat(4u);
v___x_689_ = lean_nat_mul(v_size_x27_685_, v___x_688_);
v___x_690_ = lean_unsigned_to_nat(3u);
v___x_691_ = lean_nat_div(v___x_689_, v___x_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_array_get_size(v_buckets_x27_687_);
v___x_693_ = lean_nat_dec_le(v___x_691_, v___x_692_);
lean_dec(v___x_691_);
if (v___x_693_ == 0)
{
lean_object* v_val_694_; lean_object* v___x_696_; 
v_val_694_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_687_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_val_694_);
lean_ctor_set(v___x_666_, 0, v_size_x27_685_);
v___x_696_ = v___x_666_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_size_x27_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_val_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_699_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_buckets_x27_687_);
lean_ctor_set(v___x_666_, 0, v_size_x27_685_);
v___x_699_ = v___x_666_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_size_x27_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_buckets_x27_687_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v___x_701_; lean_object* v_buckets_x27_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_inc(v_bkt_682_);
v___x_701_ = lean_box(0);
v_buckets_x27_702_ = lean_array_uset(v_buckets_664_, v___x_681_, v___x_701_);
v___x_703_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_661_, v_b_662_, v_bkt_682_);
v___x_704_ = lean_array_uset(v_buckets_x27_702_, v___x_681_, v___x_703_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_704_);
v___x_706_ = v___x_666_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_size_663_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_715_ == 0)
{
return v_b_714_;
}
else
{
lean_object* v_a_716_; lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v_r_719_; size_t v___x_720_; size_t v___x_721_; 
v_a_716_ = lean_array_uget_borrowed(v_as_711_, v_i_713_);
v_fst_717_ = lean_ctor_get(v_a_716_, 0);
v_snd_718_ = lean_ctor_get(v_a_716_, 1);
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
v_r_719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_b_714_, v_fst_717_, v_snd_718_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_713_, v___x_720_);
v_i_713_ = v___x_721_;
v_b_714_ = v_r_719_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_711_ = stack[0].m_obj;
size_t v_sz_712_ = stack[1].m_num;
size_t v_i_713_ = stack[2].m_num;
lean_object* v_b_714_ = stack[3].m_obj;
lean_object* v_res_723_;
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_711_, v_sz_712_, v_i_713_, v_b_714_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(lean_object* v_as_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_b_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_724_, v_sz_boxed_728_, v_i_boxed_729_, v_b_727_);
lean_dec_ref(v_as_724_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object* v_m_731_, lean_object* v_l_732_){
_start:
{
size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v_sz_733_ = lean_array_size(v_l_732_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_l_732_, v_sz_733_, v___x_734_, v_m_731_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object* v_m_736_, lean_object* v_l_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_736_, v_l_737_);
lean_dec_ref(v_l_737_);
return v_res_738_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_unsigned_to_nat(16u);
v___x_741_ = lean_mk_array(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
return v___x_744_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t v_pu_745_, lean_object* v_decls_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
size_t v_sz_752_; size_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_declsMap_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_sz_752_ = lean_array_size(v_decls_746_);
v___x_753_ = ((size_t)0ULL);
lean_inc_ref(v_decls_746_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_752_, v___x_753_, v_decls_746_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_box(0);
v___x_757_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
v_declsMap_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_757_, v___x_754_);
lean_dec_ref(v___x_754_);
v___x_759_ = lean_array_get_size(v_decls_746_);
v___x_760_ = lean_unsigned_to_nat(4u);
v___x_761_ = lean_nat_mul(v___x_759_, v___x_760_);
v___x_762_ = lean_unsigned_to_nat(3u);
v___x_763_ = lean_nat_div(v___x_761_, v___x_762_);
lean_dec(v___x_761_);
v___x_764_ = l_Nat_nextPowerOfTwo(v___x_763_);
lean_dec(v___x_763_);
v___x_765_ = lean_mk_array(v___x_764_, v___x_756_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_755_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_mk_empty_array_with_capacity(v___x_759_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_st_mk_ref(v___x_768_);
v___x_770_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_745_, v_decls_746_, v_declsMap_758_, v___x_769_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec_ref(v_declsMap_758_);
lean_dec_ref(v_decls_746_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_770_, 0);
lean_dec(v_unused_780_);
v___x_772_ = v___x_770_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_dec(v___x_770_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v_order_775_; lean_object* v___x_777_; 
v___x_774_ = lean_st_ref_get(v___x_769_);
lean_dec(v___x_769_);
v_order_775_ = lean_ctor_get(v___x_774_, 1);
lean_inc_ref(v_order_775_);
lean_dec(v___x_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_order_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_order_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v___x_769_);
v_a_781_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_770_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_770_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_745_ = stack[0].m_num;
lean_object* v_decls_746_ = stack[1].m_obj;
lean_object* v_a_747_ = stack[2].m_obj;
lean_object* v_a_748_ = stack[3].m_obj;
lean_object* v_a_749_ = stack[4].m_obj;
lean_object* v_a_750_ = stack[5].m_obj;
lean_object* v_res_789_;
v_res_789_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_745_, v_decls_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
stack->m_obj
 = v_res_789_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object* v_pu_790_, lean_object* v_decls_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
uint8_t v_pu_boxed_797_; lean_object* v_res_798_; 
v_pu_boxed_797_ = lean_unbox(v_pu_790_);
v_res_798_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_boxed_797_, v_decls_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object* v_00_u03b2_799_, lean_object* v_m_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_m_800_, v_a_801_, v_b_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_804_, lean_object* v_a_805_, lean_object* v_b_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_805_, v_b_806_, v_x_807_);
return v___x_808_;
}
}
lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t v_pu_809_, lean_object* v_decls_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_809_, v_decls_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
return v___x_816_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toposortDecls_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_809_ = stack[0].m_num;
lean_object* v_decls_810_ = stack[1].m_obj;
lean_object* v_a_811_ = stack[2].m_obj;
lean_object* v_a_812_ = stack[3].m_obj;
lean_object* v_a_813_ = stack[4].m_obj;
lean_object* v_a_814_ = stack[5].m_obj;
lean_object* v_res_817_;
v_res_817_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_809_, v_decls_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object* v_pu_818_, lean_object* v_decls_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
uint8_t v_pu_boxed_825_; lean_object* v_res_826_; 
v_pu_boxed_825_ = lean_unbox(v_pu_818_);
v_res_826_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_boxed_825_, v_decls_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_826_;
}
}
lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t v___x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v___x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
return v___x_834_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toposortPass___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_827_ = stack[0].m_num;
lean_object* v___y_828_ = stack[1].m_obj;
lean_object* v___y_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v___y_831_ = stack[4].m_obj;
lean_object* v___y_832_ = stack[5].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object* v___x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_28__boxed_843_; lean_object* v_res_844_; 
v___x_28__boxed_843_ = lean_unbox(v___x_836_);
v_res_844_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_28__boxed_843_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_844_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_toposortPass___closed__2(void){
_start:
{
uint8_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = 2;
v___x_849_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__3(void){
_start:
{
uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___f_852_; 
v___x_850_ = lean_uint8_once(&l_Lean_Compiler_LCNF_toposortPass___closed__2, &l_Lean_Compiler_LCNF_toposortPass___closed__2_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__2);
v___x_851_ = lean_box(v___x_850_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed), 7, 1);
lean_closure_set(v___f_852_, 0, v___x_851_);
return v___f_852_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__4(void){
_start:
{
lean_object* v___f_853_; lean_object* v___x_854_; uint8_t v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___f_853_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__3, &l_Lean_Compiler_LCNF_toposortPass___closed__3_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__3);
v___x_854_ = ((lean_object*)(l_Lean_Compiler_LCNF_toposortPass___closed__1));
v___x_855_ = 0;
v___x_856_ = 2;
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_854_);
lean_ctor_set(v___x_858_, 2, v___f_853_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*3, v___x_856_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*3 + 1, v___x_856_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*3 + 2, v___x_855_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__4, &l_Lean_Compiler_LCNF_toposortPass___closed__4_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__4);
return v___x_859_;
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
