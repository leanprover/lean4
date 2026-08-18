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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_name_eq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___y_63_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
if (lean_obj_tag(v_query_59_) == 0)
{
uint64_t v___x_78_; 
v___x_78_ = 1723ULL;
v___y_63_ = v___x_78_;
goto v___jp_62_;
}
else
{
uint64_t v_hash_79_; 
v_hash_79_ = lean_ctor_get_uint64(v_query_59_, sizeof(void*)*2);
v___y_63_ = v_hash_79_;
goto v___jp_62_;
}
v___jp_62_:
{
uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v_fold_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_64_ = 32ULL;
v___x_65_ = lean_uint64_shift_right(v___y_63_, v___x_64_);
v_fold_66_ = lean_uint64_xor(v___y_63_, v___x_65_);
v___x_67_ = 16ULL;
v___x_68_ = lean_uint64_shift_right(v_fold_66_, v___x_67_);
v___x_69_ = lean_uint64_xor(v_fold_66_, v___x_68_);
v___x_70_ = lean_uint64_to_usize(v___x_69_);
v___x_71_ = lean_usize_of_nat(v___x_61_);
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_sub(v___x_71_, v___x_72_);
v___x_74_ = lean_usize_land(v___x_70_, v___x_73_);
v___x_75_ = lean_usize_to_nat(v___x_74_);
v___x_76_ = lean_box(0);
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg(v_m_58_, v_query_59_, v___x_76_, v___x_61_, v___x_75_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg___boxed(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_m_80_, v_query_81_);
lean_dec(v_query_81_);
lean_dec_ref(v_m_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg(lean_object* v_b_83_, lean_object* v_acc_84_, lean_object* v_i_85_){
_start:
{
lean_object* v___y_87_; lean_object* v_keyArray_95_; lean_object* v_valueArray_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_keyArray_95_ = lean_ctor_get(v_b_83_, 1);
v_valueArray_96_ = lean_ctor_get(v_b_83_, 2);
v___x_97_ = lean_array_get_size(v_keyArray_95_);
v___x_98_ = lean_nat_dec_lt(v_i_85_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec(v_i_85_);
return v_acc_84_;
}
else
{
lean_object* v___x_99_; uint8_t v_isSome_100_; 
v___x_99_ = lean_array_fget_borrowed(v_keyArray_95_, v_i_85_);
v_isSome_100_ = lean_noption_is_some(v___x_99_);
if (v_isSome_100_ == 0)
{
goto v___jp_91_;
}
else
{
lean_object* v___x_101_; uint8_t v_isSome_102_; 
v___x_101_ = lean_array_fget_borrowed(v_valueArray_96_, v_i_85_);
v_isSome_102_ = lean_noption_is_some(v___x_101_);
if (v_isSome_102_ == 0)
{
goto v___jp_91_;
}
else
{
lean_object* v_val_103_; lean_object* v_val_104_; lean_object* v_i_106_; lean_object* v___x_111_; 
lean_inc(v___x_99_);
v_val_103_ = lean_noption_get(v___x_99_);
lean_inc(v___x_101_);
v_val_104_ = lean_noption_get(v___x_101_);
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_acc_84_, v_val_103_);
switch(lean_obj_tag(v___x_111_))
{
case 0:
{
lean_object* v_index_112_; lean_object* v_size_113_; lean_object* v___x_114_; 
v_index_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_index_112_);
lean_dec_ref_known(v___x_111_, 3);
v_size_113_ = lean_ctor_get(v_acc_84_, 0);
lean_inc(v_size_113_);
v___x_114_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_84_, v_size_113_, v_index_112_, v_val_103_, v_val_104_);
lean_dec(v_index_112_);
v___y_87_ = v___x_114_;
goto v___jp_86_;
}
case 1:
{
lean_object* v_index_115_; 
v_index_115_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_index_115_);
lean_dec_ref_known(v___x_111_, 1);
v_i_106_ = v_index_115_;
goto v___jp_105_;
}
default: 
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_84_, v___x_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_index_118_; 
v_index_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_index_118_);
lean_dec_ref_known(v___x_117_, 1);
v_i_106_ = v_index_118_;
goto v___jp_105_;
}
else
{
lean_dec(v_val_104_);
lean_dec(v_val_103_);
v___y_87_ = v_acc_84_;
goto v___jp_86_;
}
}
}
v___jp_105_:
{
lean_object* v_size_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_size_107_ = lean_ctor_get(v_acc_84_, 0);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_size_107_, v___x_108_);
v___x_110_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_84_, v___x_109_, v_i_106_, v_val_103_, v_val_104_);
lean_dec(v_i_106_);
v___y_87_ = v___x_110_;
goto v___jp_86_;
}
}
}
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_add(v_i_85_, v___x_88_);
lean_dec(v_i_85_);
v_acc_84_ = v___y_87_;
v_i_85_ = v___x_89_;
goto _start;
}
v___jp_91_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_i_85_, v___x_92_);
lean_dec(v_i_85_);
v_i_85_ = v___x_93_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_b_119_, lean_object* v_acc_120_, lean_object* v_i_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg(v_b_119_, v_acc_120_, v_i_121_);
lean_dec_ref(v_b_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg(lean_object* v_init_123_, lean_object* v_b_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg(v_b_124_, v_init_123_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg___boxed(lean_object* v_init_127_, lean_object* v_b_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg(v_init_127_, v_b_128_);
lean_dec_ref(v_b_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(lean_object* v_m_130_){
_start:
{
lean_object* v_keyArray_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_cellCount_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_target_138_; lean_object* v___x_139_; 
v_keyArray_131_ = lean_ctor_get(v_m_130_, 1);
v___x_132_ = lean_array_get_size(v_keyArray_131_);
v___x_133_ = lean_unsigned_to_nat(2u);
v_cellCount_134_ = lean_nat_mul(v___x_132_, v___x_133_);
v___x_135_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_134_);
v___x_136_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_134_);
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_134_);
v_target_138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_138_, 0, v___x_135_);
lean_ctor_set(v_target_138_, 1, v___x_136_);
lean_ctor_set(v_target_138_, 2, v___x_137_);
v___x_139_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg(v_target_138_, v_m_130_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg___boxed(lean_object* v_m_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_m_140_);
lean_dec_ref(v_m_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(lean_object* v_f_142_, lean_object* v_v_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
if (lean_obj_tag(v_v_143_) == 0)
{
lean_object* v_code_151_; lean_object* v___x_152_; 
v_code_151_ = lean_ctor_get(v_v_143_, 0);
lean_inc_ref(v_code_151_);
lean_dec_ref_known(v_v_143_, 1);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
v___x_152_ = lean_apply_8(v_f_142_, v_code_151_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, lean_box(0));
return v___x_152_;
}
else
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v_f_142_);
v_isSharedCheck_160_ = !lean_is_exclusive(v_v_143_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_v_143_, 0);
lean_dec(v_unused_161_);
v___x_154_ = v_v_143_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_dec(v_v_143_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 0);
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg___boxed(lean_object* v_f_162_, lean_object* v_v_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_f_162_, v_v_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(lean_object* v_m_172_, lean_object* v_query_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_m_172_, v_query_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_index_175_; lean_object* v_key_176_; lean_object* v_value_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_index_175_ = lean_ctor_get(v___x_174_, 0);
v_key_176_ = lean_ctor_get(v___x_174_, 1);
v_value_177_ = lean_ctor_get(v___x_174_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_174_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_value_177_);
lean_inc(v_key_176_);
lean_inc(v_index_175_);
lean_dec(v___x_174_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_index_175_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_key_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_value_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v___x_185_; 
lean_dec(v___x_174_);
v___x_185_ = lean_box(1);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg___boxed(lean_object* v_m_186_, lean_object* v_query_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_m_186_, v_query_187_);
lean_dec(v_query_187_);
lean_dec_ref(v_m_186_);
return v_res_188_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(lean_object* v_m_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_m_189_, v_a_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
uint8_t v___x_192_; 
lean_dec_ref_known(v___x_191_, 3);
v___x_192_ = 1;
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_m_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg(lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_m_198_, v_a_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_value_201_; lean_object* v___x_202_; 
v_value_201_ = lean_ctor_get(v___x_200_, 2);
lean_inc(v_value_201_);
lean_dec_ref_known(v___x_200_, 3);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v_value_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg___boxed(lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg(v_m_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_m_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(lean_object* v_pu_207_, lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v_pu_boxed_216_; lean_object* v_res_217_; 
v_pu_boxed_216_ = lean_unbox(v_pu_207_);
v_res_217_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(v_pu_boxed_216_, v_x_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec_ref(v_x_208_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(uint8_t v_pu_218_, lean_object* v_decl_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___y_228_; lean_object* v___y_244_; lean_object* v___x_247_; lean_object* v_toSignature_248_; lean_object* v_seen_249_; lean_object* v_value_250_; lean_object* v_name_251_; uint8_t v___x_252_; 
v___x_247_ = lean_st_ref_get(v_a_221_);
v_toSignature_248_ = lean_ctor_get(v_decl_219_, 0);
v_seen_249_ = lean_ctor_get(v___x_247_, 0);
lean_inc_ref(v_seen_249_);
lean_dec(v___x_247_);
v_value_250_ = lean_ctor_get(v_decl_219_, 1);
v_name_251_ = lean_ctor_get(v_toSignature_248_, 0);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_seen_249_, v_name_251_);
lean_dec_ref(v_seen_249_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_env_255_; lean_object* v_seen_256_; lean_object* v_order_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_334_; 
v___x_253_ = lean_st_ref_get(v_a_225_);
v___x_254_ = lean_st_ref_take(v_a_221_);
v_env_255_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_env_255_);
lean_dec(v___x_253_);
v_seen_256_ = lean_ctor_get(v___x_254_, 0);
v_order_257_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_334_ == 0)
{
v___x_259_ = v___x_254_;
v_isShared_260_ = v_isSharedCheck_334_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_order_257_);
lean_inc(v_seen_256_);
lean_dec(v___x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_334_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___y_264_; lean_object* v___x_272_; lean_object* v___y_274_; lean_object* v_i_275_; lean_object* v___y_281_; lean_object* v___y_291_; lean_object* v_i_292_; lean_object* v___x_307_; 
v___x_261_ = lean_box(v_pu_218_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed), 9, 1);
lean_closure_set(v___f_262_, 0, v___x_261_);
v___x_272_ = lean_box(0);
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_seen_256_, v_name_251_);
switch(lean_obj_tag(v___x_307_))
{
case 0:
{
lean_dec_ref_known(v___x_307_, 3);
v___y_264_ = v_seen_256_;
goto v___jp_263_;
}
case 1:
{
lean_object* v_index_308_; lean_object* v_size_309_; lean_object* v_keyArray_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_index_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_index_308_);
lean_dec_ref_known(v___x_307_, 1);
v_size_309_ = lean_ctor_get(v_seen_256_, 0);
v_keyArray_310_ = lean_ctor_get(v_seen_256_, 1);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v_size_309_, v___x_311_);
v___x_313_ = lean_array_get_size(v_keyArray_310_);
v___x_314_ = lean_nat_dec_lt(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec(v___x_312_);
lean_dec(v_index_308_);
goto v___jp_297_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_315_ = lean_unsigned_to_nat(4u);
v___x_316_ = lean_nat_mul(v___x_312_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(3u);
v___x_318_ = lean_nat_mul(v___x_313_, v___x_317_);
v___x_319_ = lean_nat_dec_le(v___x_316_, v___x_318_);
lean_dec(v___x_318_);
lean_dec(v___x_316_);
if (v___x_319_ == 0)
{
lean_dec(v___x_312_);
lean_dec(v_index_308_);
goto v___jp_297_;
}
else
{
lean_object* v___x_320_; 
lean_inc(v_name_251_);
v___x_320_ = l_Std_DHashMap_Raw_setEntry___redArg(v_seen_256_, v___x_312_, v_index_308_, v_name_251_, v___x_272_);
lean_dec(v_index_308_);
v___y_264_ = v___x_320_;
goto v___jp_263_;
}
}
}
default: 
{
lean_object* v_size_321_; lean_object* v_keyArray_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_size_321_ = lean_ctor_get(v_seen_256_, 0);
v_keyArray_322_ = lean_ctor_get(v_seen_256_, 1);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_add(v_size_321_, v___x_323_);
v___x_325_ = lean_array_get_size(v_keyArray_322_);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec(v___x_324_);
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_seen_256_);
lean_dec_ref(v_seen_256_);
v___y_281_ = v___x_327_;
goto v___jp_280_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_328_ = lean_unsigned_to_nat(4u);
v___x_329_ = lean_nat_mul(v___x_324_, v___x_328_);
lean_dec(v___x_324_);
v___x_330_ = lean_unsigned_to_nat(3u);
v___x_331_ = lean_nat_mul(v___x_325_, v___x_330_);
v___x_332_ = lean_nat_dec_le(v___x_329_, v___x_331_);
lean_dec(v___x_331_);
lean_dec(v___x_329_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_seen_256_);
lean_dec_ref(v_seen_256_);
v___y_281_ = v___x_333_;
goto v___jp_280_;
}
else
{
v___y_281_ = v_seen_256_;
goto v___jp_280_;
}
}
}
}
v___jp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___y_264_);
v___x_266_ = v___x_259_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___y_264_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_order_257_);
v___x_266_ = v_reuseFailAlloc_271_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_st_ref_put(v_a_221_, v___x_266_);
lean_inc_ref(v_value_250_);
v___x_268_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v___f_262_, v_value_250_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; 
lean_dec_ref_known(v___x_268_, 1);
lean_inc(v_name_251_);
lean_inc_ref(v_env_255_);
v___x_269_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_255_, v_name_251_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_270_; 
lean_inc(v_name_251_);
v___x_270_ = lean_get_init_fn_name_for(v_env_255_, v_name_251_);
v___y_244_ = v___x_270_;
goto v___jp_243_;
}
else
{
lean_dec_ref(v_env_255_);
v___y_244_ = v___x_269_;
goto v___jp_243_;
}
}
else
{
lean_dec_ref(v_env_255_);
lean_dec_ref(v_decl_219_);
return v___x_268_;
}
}
}
v___jp_273_:
{
lean_object* v_size_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_size_276_ = lean_ctor_get(v___y_274_, 0);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_size_276_, v___x_277_);
lean_inc(v_name_251_);
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_274_, v___x_278_, v_i_275_, v_name_251_, v___x_272_);
lean_dec(v_i_275_);
v___y_264_ = v___x_279_;
goto v___jp_263_;
}
v___jp_280_:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___y_281_, v_name_251_);
switch(lean_obj_tag(v___x_282_))
{
case 0:
{
lean_object* v_index_283_; lean_object* v_size_284_; lean_object* v___x_285_; 
v_index_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_283_);
lean_dec_ref_known(v___x_282_, 3);
v_size_284_ = lean_ctor_get(v___y_281_, 0);
lean_inc(v_size_284_);
lean_inc(v_name_251_);
v___x_285_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_281_, v_size_284_, v_index_283_, v_name_251_, v___x_272_);
lean_dec(v_index_283_);
v___y_264_ = v___x_285_;
goto v___jp_263_;
}
case 1:
{
lean_object* v_index_286_; 
v_index_286_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_286_);
lean_dec_ref_known(v___x_282_, 1);
v___y_274_ = v___y_281_;
v_i_275_ = v_index_286_;
goto v___jp_273_;
}
default: 
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_281_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_index_289_; 
v_index_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_index_289_);
lean_dec_ref_known(v___x_288_, 1);
v___y_274_ = v___y_281_;
v_i_275_ = v_index_289_;
goto v___jp_273_;
}
else
{
v___y_264_ = v___y_281_;
goto v___jp_263_;
}
}
}
}
v___jp_290_:
{
lean_object* v_size_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_size_293_ = lean_ctor_get(v___y_291_, 0);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_size_293_, v___x_294_);
lean_inc(v_name_251_);
v___x_296_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_291_, v___x_295_, v_i_292_, v_name_251_, v___x_272_);
lean_dec(v_i_292_);
v___y_264_ = v___x_296_;
goto v___jp_263_;
}
v___jp_297_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_seen_256_);
lean_dec_ref(v_seen_256_);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___x_298_, v_name_251_);
switch(lean_obj_tag(v___x_299_))
{
case 0:
{
lean_object* v_index_300_; lean_object* v_size_301_; lean_object* v___x_302_; 
v_index_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_299_, 3);
v_size_301_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_size_301_);
lean_inc(v_name_251_);
v___x_302_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_298_, v_size_301_, v_index_300_, v_name_251_, v___x_272_);
lean_dec(v_index_300_);
v___y_264_ = v___x_302_;
goto v___jp_263_;
}
case 1:
{
lean_object* v_index_303_; 
v_index_303_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_303_);
lean_dec_ref_known(v___x_299_, 1);
v___y_291_ = v___x_298_;
v_i_292_ = v_index_303_;
goto v___jp_290_;
}
default: 
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_298_, v___x_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_index_306_; 
v_index_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_index_306_);
lean_dec_ref_known(v___x_305_, 1);
v___y_291_ = v___x_298_;
v_i_292_ = v_index_306_;
goto v___jp_290_;
}
else
{
v___y_264_ = v___x_298_;
goto v___jp_263_;
}
}
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_decl_219_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v_seen_230_; lean_object* v_order_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_242_; 
v___x_229_ = lean_st_ref_take(v___y_228_);
v_seen_230_ = lean_ctor_get(v___x_229_, 0);
v_order_231_ = lean_ctor_get(v___x_229_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_242_ == 0)
{
v___x_233_ = v___x_229_;
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_order_231_);
lean_inc(v_seen_230_);
lean_dec(v___x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_array_push(v_order_231_, v_decl_219_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_seen_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_put(v___y_228_, v___x_237_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
v___jp_243_:
{
if (lean_obj_tag(v___y_244_) == 1)
{
lean_object* v_val_245_; lean_object* v___x_246_; 
v_val_245_ = lean_ctor_get(v___y_244_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v___y_244_, 1);
v___x_246_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_218_, v_val_245_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_val_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_dec_ref_known(v___x_246_, 1);
v___y_228_ = v_a_221_;
goto v___jp_227_;
}
else
{
lean_dec_ref(v_decl_219_);
return v___x_246_;
}
}
else
{
lean_dec(v___y_244_);
v___y_228_ = v_a_221_;
goto v___jp_227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(uint8_t v_pu_337_, lean_object* v_declName_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg(v_a_339_, v_declName_338_);
if (lean_obj_tag(v___x_346_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_348_; 
v_val_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_337_, v_val_347_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(uint8_t v_pu_351_, lean_object* v_code_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
if (lean_obj_tag(v_code_352_) == 0)
{
lean_object* v_decl_360_; lean_object* v_value_361_; 
v_decl_360_ = lean_ctor_get(v_code_352_, 0);
v_value_361_ = lean_ctor_get(v_decl_360_, 3);
switch(lean_obj_tag(v_value_361_))
{
case 3:
{
lean_object* v_declName_362_; lean_object* v___x_363_; 
v_declName_362_ = lean_ctor_get(v_value_361_, 0);
v___x_363_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_351_, v_declName_362_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_363_;
}
case 9:
{
lean_object* v_fn_364_; lean_object* v___x_365_; 
v_fn_364_ = lean_ctor_get(v_value_361_, 0);
v___x_365_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_351_, v_fn_364_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_365_;
}
case 10:
{
lean_object* v_fn_366_; lean_object* v___x_367_; 
v_fn_366_ = lean_ctor_get(v_value_361_, 0);
v___x_367_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_351_, v_fn_366_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_367_;
}
default: 
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_box(0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(uint8_t v_pu_372_, uint8_t v_pu_373_, lean_object* v_as_374_, size_t v_i_375_, size_t v_stop_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___y_386_; uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_eq(v_i_375_, v_stop_376_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_array_uget_borrowed(v_as_374_, v_i_375_);
switch(lean_obj_tag(v___x_392_))
{
case 0:
{
lean_object* v_code_393_; lean_object* v___x_394_; 
v_code_393_ = lean_ctor_get(v___x_392_, 2);
v___x_394_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_372_, v_pu_373_, v_code_393_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
v___y_386_ = v___x_394_;
goto v___jp_385_;
}
case 1:
{
lean_object* v_code_395_; lean_object* v___x_396_; 
v_code_395_ = lean_ctor_get(v___x_392_, 1);
v___x_396_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_372_, v_pu_373_, v_code_395_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
default: 
{
lean_object* v_code_397_; lean_object* v___x_398_; 
v_code_397_ = lean_ctor_get(v___x_392_, 0);
v___x_398_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_372_, v_pu_373_, v_code_397_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
v___y_386_ = v___x_398_;
goto v___jp_385_;
}
}
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_b_377_);
return v___x_399_;
}
v___jp_385_:
{
if (lean_obj_tag(v___y_386_) == 0)
{
lean_object* v_a_387_; size_t v___x_388_; size_t v___x_389_; 
v_a_387_ = lean_ctor_get(v___y_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___y_386_, 1);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_375_, v___x_388_);
v_i_375_ = v___x_389_;
v_b_377_ = v_a_387_;
goto _start;
}
else
{
return v___y_386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(uint8_t v_pu_400_, uint8_t v_pu_401_, lean_object* v_c_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_400_, v_c_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v___x_410_, 0);
lean_dec(v_unused_464_);
v___x_412_ = v___x_410_;
v_isShared_413_ = v_isSharedCheck_463_;
goto v_resetjp_411_;
}
else
{
lean_dec(v___x_410_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_463_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
switch(lean_obj_tag(v_c_402_))
{
case 0:
{
lean_object* v_k_414_; 
lean_del_object(v___x_412_);
v_k_414_ = lean_ctor_get(v_c_402_, 1);
v_c_402_ = v_k_414_;
goto _start;
}
case 1:
{
lean_object* v_decl_416_; lean_object* v_k_417_; lean_object* v_value_418_; lean_object* v___x_419_; 
lean_del_object(v___x_412_);
v_decl_416_ = lean_ctor_get(v_c_402_, 0);
v_k_417_ = lean_ctor_get(v_c_402_, 1);
v_value_418_ = lean_ctor_get(v_decl_416_, 4);
v___x_419_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_400_, v_pu_401_, v_value_418_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_dec_ref_known(v___x_419_, 1);
v_c_402_ = v_k_417_;
goto _start;
}
else
{
return v___x_419_;
}
}
case 2:
{
lean_object* v_decl_421_; lean_object* v_k_422_; lean_object* v_value_423_; lean_object* v___x_424_; 
lean_del_object(v___x_412_);
v_decl_421_ = lean_ctor_get(v_c_402_, 0);
v_k_422_ = lean_ctor_get(v_c_402_, 1);
v_value_423_ = lean_ctor_get(v_decl_421_, 4);
v___x_424_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_400_, v_pu_401_, v_value_423_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_dec_ref_known(v___x_424_, 1);
v_c_402_ = v_k_422_;
goto _start;
}
else
{
return v___x_424_;
}
}
case 4:
{
lean_object* v_cases_426_; lean_object* v_alts_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_cases_426_ = lean_ctor_get(v_c_402_, 0);
v_alts_427_ = lean_ctor_get(v_cases_426_, 3);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_array_get_size(v_alts_427_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_433_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_430_);
v___x_433_ = v___x_412_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_430_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
uint8_t v___x_435_; 
v___x_435_ = lean_nat_dec_le(v___x_429_, v___x_429_);
if (v___x_435_ == 0)
{
if (v___x_431_ == 0)
{
lean_object* v___x_437_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_430_);
v___x_437_ = v___x_412_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_430_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
lean_del_object(v___x_412_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_429_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_400_, v_pu_401_, v_alts_427_, v___x_439_, v___x_440_, v___x_430_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_441_;
}
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
lean_del_object(v___x_412_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_429_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_400_, v_pu_401_, v_alts_427_, v___x_442_, v___x_443_, v___x_430_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_444_;
}
}
}
case 7:
{
lean_object* v_k_445_; 
lean_del_object(v___x_412_);
v_k_445_ = lean_ctor_get(v_c_402_, 3);
v_c_402_ = v_k_445_;
goto _start;
}
case 8:
{
lean_object* v_k_447_; 
lean_del_object(v___x_412_);
v_k_447_ = lean_ctor_get(v_c_402_, 3);
v_c_402_ = v_k_447_;
goto _start;
}
case 9:
{
lean_object* v_k_449_; 
lean_del_object(v___x_412_);
v_k_449_ = lean_ctor_get(v_c_402_, 5);
v_c_402_ = v_k_449_;
goto _start;
}
case 10:
{
lean_object* v_k_451_; 
lean_del_object(v___x_412_);
v_k_451_ = lean_ctor_get(v_c_402_, 2);
v_c_402_ = v_k_451_;
goto _start;
}
case 11:
{
lean_object* v_k_453_; 
lean_del_object(v___x_412_);
v_k_453_ = lean_ctor_get(v_c_402_, 2);
v_c_402_ = v_k_453_;
goto _start;
}
case 12:
{
lean_object* v_k_455_; 
lean_del_object(v___x_412_);
v_k_455_ = lean_ctor_get(v_c_402_, 3);
v_c_402_ = v_k_455_;
goto _start;
}
case 13:
{
lean_object* v_k_457_; 
lean_del_object(v___x_412_);
v_k_457_ = lean_ctor_get(v_c_402_, 1);
v_c_402_ = v_k_457_;
goto _start;
}
default: 
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_459_);
v___x_461_ = v___x_412_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
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
else
{
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(uint8_t v_pu_465_, lean_object* v_x_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_465_, v_pu_465_, v_x_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(lean_object* v_pu_475_, lean_object* v_declName_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
uint8_t v_pu_boxed_484_; lean_object* v_res_485_; 
v_pu_boxed_484_ = lean_unbox(v_pu_475_);
v_res_485_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_boxed_484_, v_declName_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_declName_476_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(lean_object* v_pu_486_, lean_object* v_code_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
uint8_t v_pu_boxed_495_; lean_object* v_res_496_; 
v_pu_boxed_495_ = lean_unbox(v_pu_486_);
v_res_496_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_boxed_495_, v_code_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_code_487_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(lean_object* v_pu_497_, lean_object* v_pu_498_, lean_object* v_as_499_, lean_object* v_i_500_, lean_object* v_stop_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
uint8_t v_pu_boxed_510_; uint8_t v_pu_boxed_511_; size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v_pu_boxed_510_ = lean_unbox(v_pu_497_);
v_pu_boxed_511_ = lean_unbox(v_pu_498_);
v_i_boxed_512_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_501_);
lean_dec(v_stop_501_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_510_, v_pu_boxed_511_, v_as_499_, v_i_boxed_512_, v_stop_boxed_513_, v_b_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v_as_499_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(lean_object* v_pu_515_, lean_object* v_pu_516_, lean_object* v_c_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_pu_boxed_525_; uint8_t v_pu_boxed_526_; lean_object* v_res_527_; 
v_pu_boxed_525_ = lean_unbox(v_pu_515_);
v_pu_boxed_526_ = lean_unbox(v_pu_516_);
v_res_527_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_525_, v_pu_boxed_526_, v_c_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_c_517_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(lean_object* v_pu_528_, lean_object* v_decl_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
uint8_t v_pu_boxed_537_; lean_object* v_res_538_; 
v_pu_boxed_537_ = lean_unbox(v_pu_528_);
v_res_538_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_boxed_537_, v_decl_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(uint8_t v_pu_539_, lean_object* v_f_540_, lean_object* v_v_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_f_540_, v_v_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___boxed(lean_object* v_pu_550_, lean_object* v_f_551_, lean_object* v_v_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v_pu_boxed_560_; lean_object* v_res_561_; 
v_pu_boxed_560_ = lean_unbox(v_pu_550_);
v_res_561_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(v_pu_boxed_560_, v_f_551_, v_v_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_561_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(lean_object* v_00_u03b2_562_, lean_object* v_m_563_, lean_object* v_a_564_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_563_, v_a_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(lean_object* v_00_u03b2_566_, lean_object* v_m_567_, lean_object* v_a_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_566_, v_m_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_m_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(lean_object* v_00_u03b2_571_, lean_object* v_m_572_, lean_object* v_query_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_m_572_, v_query_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(lean_object* v_00_u03b2_575_, lean_object* v_m_576_, lean_object* v_query_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_00_u03b2_575_, v_m_576_, v_query_577_);
lean_dec(v_query_577_);
lean_dec_ref(v_m_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4(lean_object* v_00_u03b2_579_, lean_object* v_m_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_m_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___boxed(lean_object* v_00_u03b2_582_, lean_object* v_m_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4(v_00_u03b2_582_, v_m_583_);
lean_dec_ref(v_m_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6(lean_object* v_00_u03b2_585_, lean_object* v_m_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___redArg(v_m_586_, v_a_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6___boxed(lean_object* v_00_u03b2_589_, lean_object* v_m_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__6(v_00_u03b2_589_, v_m_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_m_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(lean_object* v_00_u03b2_593_, lean_object* v_m_594_, lean_object* v_query_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_m_594_, v_query_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_query_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_597_, v_m_598_, v_query_599_);
lean_dec(v_query_599_);
lean_dec_ref(v_m_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6(lean_object* v_00_u03b2_601_, lean_object* v_m_602_, lean_object* v_query_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___redArg(v_m_602_, v_query_603_, v_x_604_, v_x_605_, v_x_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6___boxed(lean_object* v_00_u03b2_609_, lean_object* v_m_610_, lean_object* v_query_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3_spec__6(v_00_u03b2_609_, v_m_610_, v_query_611_, v_x_612_, v_x_613_, v_x_614_, v_x_615_);
lean_dec(v_query_611_);
lean_dec_ref(v_m_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8(lean_object* v_00_u03b2_617_, lean_object* v_init_618_, lean_object* v_b_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___redArg(v_init_618_, v_b_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8___boxed(lean_object* v_00_u03b2_621_, lean_object* v_init_622_, lean_object* v_b_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8(v_00_u03b2_621_, v_init_622_, v_b_623_);
lean_dec_ref(v_b_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10(lean_object* v_00_u03b2_625_, lean_object* v_b_626_, lean_object* v_acc_627_, lean_object* v_i_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___redArg(v_b_626_, v_acc_627_, v_i_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b2_630_, lean_object* v_b_631_, lean_object* v_acc_632_, lean_object* v_i_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4_spec__8_spec__10(v_00_u03b2_630_, v_b_631_, v_acc_632_, v_i_633_);
lean_dec_ref(v_b_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(uint8_t v_pu_635_, lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
lean_inc(v___x_648_);
v___x_649_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_635_, v___x_648_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; size_t v___x_651_; size_t v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_637_, v___x_651_);
v_i_637_ = v___x_652_;
v_b_639_ = v_a_650_;
goto _start;
}
else
{
return v___x_649_;
}
}
else
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_b_639_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(lean_object* v_pu_655_, lean_object* v_as_656_, lean_object* v_i_657_, lean_object* v_stop_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v_pu_boxed_667_; size_t v_i_boxed_668_; size_t v_stop_boxed_669_; lean_object* v_res_670_; 
v_pu_boxed_667_ = lean_unbox(v_pu_655_);
v_i_boxed_668_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_stop_boxed_669_ = lean_unbox_usize(v_stop_658_);
lean_dec(v_stop_658_);
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_667_, v_as_656_, v_i_boxed_668_, v_stop_boxed_669_, v_b_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v_as_656_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(uint8_t v_pu_671_, lean_object* v_decls_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_decls_672_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_le(v___x_681_, v___x_681_);
if (v___x_685_ == 0)
{
if (v___x_683_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_682_);
return v___x_686_;
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_681_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_671_, v_decls_672_, v___x_687_, v___x_688_, v___x_682_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v___x_689_;
}
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_681_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_671_, v_decls_672_, v___x_690_, v___x_691_, v___x_682_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(lean_object* v_pu_693_, lean_object* v_decls_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_pu_boxed_702_; lean_object* v_res_703_; 
v_pu_boxed_702_ = lean_unbox(v_pu_693_);
v_res_703_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_boxed_702_, v_decls_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_decls_694_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(size_t v_sz_704_, size_t v_i_705_, lean_object* v_bs_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_lt(v_i_705_, v_sz_704_);
if (v___x_707_ == 0)
{
return v_bs_706_;
}
else
{
lean_object* v_v_708_; lean_object* v_toSignature_709_; lean_object* v_name_710_; lean_object* v___x_711_; lean_object* v_bs_x27_712_; lean_object* v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v_v_708_ = lean_array_uget(v_bs_706_, v_i_705_);
v_toSignature_709_ = lean_ctor_get(v_v_708_, 0);
v_name_710_ = lean_ctor_get(v_toSignature_709_, 0);
lean_inc(v_name_710_);
v___x_711_ = lean_unsigned_to_nat(0u);
v_bs_x27_712_ = lean_array_uset(v_bs_706_, v_i_705_, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_name_710_);
lean_ctor_set(v___x_713_, 1, v_v_708_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_705_, v___x_714_);
v___x_716_ = lean_array_uset(v_bs_x27_712_, v_i_705_, v___x_713_);
v_i_705_ = v___x_715_;
v_bs_706_ = v___x_716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_bs_720_){
_start:
{
size_t v_sz_boxed_721_; size_t v_i_boxed_722_; lean_object* v_res_723_; 
v_sz_boxed_721_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_722_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_721_, v_i_boxed_722_, v_bs_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(lean_object* v_as_724_, size_t v_sz_725_, size_t v_i_726_, lean_object* v_b_727_){
_start:
{
lean_object* v___y_729_; uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_lt(v_i_726_, v_sz_725_);
if (v___x_733_ == 0)
{
return v_b_727_;
}
else
{
lean_object* v_a_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___y_738_; lean_object* v_i_739_; lean_object* v___y_745_; lean_object* v___y_755_; lean_object* v_i_756_; lean_object* v___x_771_; 
v_a_734_ = lean_array_uget_borrowed(v_as_724_, v_i_726_);
v_fst_735_ = lean_ctor_get(v_a_734_, 0);
v_snd_736_ = lean_ctor_get(v_a_734_, 1);
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_b_727_, v_fst_735_);
switch(lean_obj_tag(v___x_771_))
{
case 0:
{
lean_object* v_index_772_; lean_object* v_size_773_; lean_object* v___x_774_; 
v_index_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_index_772_);
lean_dec_ref_known(v___x_771_, 3);
v_size_773_ = lean_ctor_get(v_b_727_, 0);
lean_inc(v_size_773_);
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
v___x_774_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_727_, v_size_773_, v_index_772_, v_fst_735_, v_snd_736_);
lean_dec(v_index_772_);
v___y_729_ = v___x_774_;
goto v___jp_728_;
}
case 1:
{
lean_object* v_index_775_; lean_object* v_size_776_; lean_object* v_keyArray_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_index_775_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_index_775_);
lean_dec_ref_known(v___x_771_, 1);
v_size_776_ = lean_ctor_get(v_b_727_, 0);
v_keyArray_777_ = lean_ctor_get(v_b_727_, 1);
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_nat_add(v_size_776_, v___x_778_);
v___x_780_ = lean_array_get_size(v_keyArray_777_);
v___x_781_ = lean_nat_dec_lt(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v___x_779_);
lean_dec(v_index_775_);
goto v___jp_761_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_782_ = lean_unsigned_to_nat(4u);
v___x_783_ = lean_nat_mul(v___x_779_, v___x_782_);
v___x_784_ = lean_unsigned_to_nat(3u);
v___x_785_ = lean_nat_mul(v___x_780_, v___x_784_);
v___x_786_ = lean_nat_dec_le(v___x_783_, v___x_785_);
lean_dec(v___x_785_);
lean_dec(v___x_783_);
if (v___x_786_ == 0)
{
lean_dec(v___x_779_);
lean_dec(v_index_775_);
goto v___jp_761_;
}
else
{
lean_object* v___x_787_; 
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
v___x_787_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_727_, v___x_779_, v_index_775_, v_fst_735_, v_snd_736_);
lean_dec(v_index_775_);
v___y_729_ = v___x_787_;
goto v___jp_728_;
}
}
}
default: 
{
lean_object* v_size_788_; lean_object* v_keyArray_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_size_788_ = lean_ctor_get(v_b_727_, 0);
v_keyArray_789_ = lean_ctor_get(v_b_727_, 1);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v_size_788_, v___x_790_);
v___x_792_ = lean_array_get_size(v_keyArray_789_);
v___x_793_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v___x_791_);
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_b_727_);
lean_dec_ref(v_b_727_);
v___y_745_ = v___x_794_;
goto v___jp_744_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_795_ = lean_unsigned_to_nat(4u);
v___x_796_ = lean_nat_mul(v___x_791_, v___x_795_);
lean_dec(v___x_791_);
v___x_797_ = lean_unsigned_to_nat(3u);
v___x_798_ = lean_nat_mul(v___x_792_, v___x_797_);
v___x_799_ = lean_nat_dec_le(v___x_796_, v___x_798_);
lean_dec(v___x_798_);
lean_dec(v___x_796_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_b_727_);
lean_dec_ref(v_b_727_);
v___y_745_ = v___x_800_;
goto v___jp_744_;
}
else
{
v___y_745_ = v_b_727_;
goto v___jp_744_;
}
}
}
}
v___jp_737_:
{
lean_object* v_size_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_size_740_ = lean_ctor_get(v___y_738_, 0);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v_size_740_, v___x_741_);
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
v___x_743_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_738_, v___x_742_, v_i_739_, v_fst_735_, v_snd_736_);
lean_dec(v_i_739_);
v___y_729_ = v___x_743_;
goto v___jp_728_;
}
v___jp_744_:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___y_745_, v_fst_735_);
switch(lean_obj_tag(v___x_746_))
{
case 0:
{
lean_object* v_index_747_; lean_object* v_size_748_; lean_object* v___x_749_; 
v_index_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_index_747_);
lean_dec_ref_known(v___x_746_, 3);
v_size_748_ = lean_ctor_get(v___y_745_, 0);
lean_inc(v_size_748_);
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
v___x_749_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_745_, v_size_748_, v_index_747_, v_fst_735_, v_snd_736_);
lean_dec(v_index_747_);
v___y_729_ = v___x_749_;
goto v___jp_728_;
}
case 1:
{
lean_object* v_index_750_; 
v_index_750_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_index_750_);
lean_dec_ref_known(v___x_746_, 1);
v___y_738_ = v___y_745_;
v_i_739_ = v_index_750_;
goto v___jp_737_;
}
default: 
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_745_, v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_index_753_; 
v_index_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_753_);
lean_dec_ref_known(v___x_752_, 1);
v___y_738_ = v___y_745_;
v_i_739_ = v_index_753_;
goto v___jp_737_;
}
else
{
v___y_729_ = v___y_745_;
goto v___jp_728_;
}
}
}
}
v___jp_754_:
{
lean_object* v_size_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_size_757_ = lean_ctor_get(v___y_755_, 0);
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_add(v_size_757_, v___x_758_);
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
v___x_760_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_755_, v___x_759_, v_i_756_, v_fst_735_, v_snd_736_);
lean_dec(v_i_756_);
v___y_729_ = v___x_760_;
goto v___jp_728_;
}
v___jp_761_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__4___redArg(v_b_727_);
lean_dec_ref(v_b_727_);
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___x_762_, v_fst_735_);
switch(lean_obj_tag(v___x_763_))
{
case 0:
{
lean_object* v_index_764_; lean_object* v_size_765_; lean_object* v___x_766_; 
v_index_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_index_764_);
lean_dec_ref_known(v___x_763_, 3);
v_size_765_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_size_765_);
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
v___x_766_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_762_, v_size_765_, v_index_764_, v_fst_735_, v_snd_736_);
lean_dec(v_index_764_);
v___y_729_ = v___x_766_;
goto v___jp_728_;
}
case 1:
{
lean_object* v_index_767_; 
v_index_767_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_index_767_);
lean_dec_ref_known(v___x_763_, 1);
v___y_755_ = v___x_762_;
v_i_756_ = v_index_767_;
goto v___jp_754_;
}
default: 
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_762_, v___x_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_index_770_; 
v_index_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_index_770_);
lean_dec_ref_known(v___x_769_, 1);
v___y_755_ = v___x_762_;
v_i_756_ = v_index_770_;
goto v___jp_754_;
}
else
{
v___y_729_ = v___x_762_;
goto v___jp_728_;
}
}
}
}
}
v___jp_728_:
{
size_t v___x_730_; size_t v___x_731_; 
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_726_, v___x_730_);
v_i_726_ = v___x_731_;
v_b_727_ = v___y_729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___boxed(lean_object* v_as_801_, lean_object* v_sz_802_, lean_object* v_i_803_, lean_object* v_b_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_802_);
lean_dec(v_sz_802_);
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(v_as_801_, v_sz_boxed_805_, v_i_boxed_806_, v_b_804_);
lean_dec_ref(v_as_801_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(lean_object* v_m_808_, lean_object* v_l_809_){
_start:
{
size_t v_sz_810_; size_t v___x_811_; lean_object* v___x_812_; 
v_sz_810_ = lean_array_size(v_l_809_);
v___x_811_ = ((size_t)0ULL);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(v_l_809_, v_sz_810_, v___x_811_, v_m_808_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(lean_object* v_m_813_, lean_object* v_l_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_813_, v_l_814_);
lean_dec_ref(v_l_814_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0(void){
_start:
{
lean_object* v_cellCount_816_; lean_object* v___x_817_; 
v_cellCount_816_ = lean_unsigned_to_nat(16u);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_816_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1(void){
_start:
{
lean_object* v_cellCount_818_; lean_object* v___x_819_; 
v_cellCount_818_ = lean_unsigned_to_nat(16u);
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_818_);
return v___x_819_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__2(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_820_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
v___x_821_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(uint8_t v_pu_824_, lean_object* v_decls_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_cellCount_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; size_t v_sz_847_; size_t v___x_848_; lean_object* v___x_849_; lean_object* v_declsMap_850_; lean_object* v___x_851_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__2, &l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__2_once, _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__2);
v___x_833_ = lean_array_get_size(v_decls_825_);
v___x_834_ = lean_unsigned_to_nat(4u);
v___x_835_ = lean_nat_mul(v___x_833_, v___x_834_);
v___x_836_ = lean_unsigned_to_nat(2u);
v___x_837_ = lean_nat_add(v___x_835_, v___x_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_unsigned_to_nat(3u);
v___x_839_ = lean_nat_div(v___x_837_, v___x_838_);
lean_dec(v___x_837_);
v_cellCount_840_ = l_Nat_nextPowerOfTwo(v___x_839_);
lean_dec(v___x_839_);
lean_inc(v_cellCount_840_);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_840_);
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_840_);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v___x_831_);
lean_ctor_set(v___x_843_, 1, v___x_841_);
lean_ctor_set(v___x_843_, 2, v___x_842_);
v___x_844_ = lean_mk_empty_array_with_capacity(v___x_833_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_st_mk_ref(v___x_845_);
v_sz_847_ = lean_array_size(v_decls_825_);
v___x_848_ = ((size_t)0ULL);
lean_inc_ref(v_decls_825_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_847_, v___x_848_, v_decls_825_);
v_declsMap_850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_832_, v___x_849_);
lean_dec_ref(v___x_849_);
v___x_851_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(v_pu_824_, v_decls_825_, v_declsMap_850_, v___x_846_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec_ref(v_declsMap_850_);
lean_dec_ref(v_decls_825_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_860_; 
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_861_);
v___x_853_ = v___x_851_;
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
else
{
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v_order_856_; lean_object* v___x_858_; 
v___x_855_ = lean_st_ref_get(v___x_846_);
lean_dec(v___x_846_);
v_order_856_ = lean_ctor_get(v___x_855_, 1);
lean_inc_ref(v_order_856_);
lean_dec(v___x_855_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_order_856_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_order_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v___x_846_);
v_a_862_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_851_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_851_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(lean_object* v_pu_870_, lean_object* v_decls_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
uint8_t v_pu_boxed_877_; lean_object* v_res_878_; 
v_pu_boxed_877_ = lean_unbox(v_pu_870_);
v_res_878_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_boxed_877_, v_decls_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls(uint8_t v_pu_879_, lean_object* v_decls_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v_pu_879_, v_decls_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortDecls___boxed(lean_object* v_pu_887_, lean_object* v_decls_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_pu_boxed_894_; lean_object* v_res_895_; 
v_pu_boxed_894_ = lean_unbox(v_pu_887_);
v_res_895_ = l_Lean_Compiler_LCNF_toposortDecls(v_pu_boxed_894_, v_decls_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0(uint8_t v___x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(v___x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(lean_object* v___x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_28__boxed_911_; lean_object* v_res_912_; 
v___x_28__boxed_911_ = lean_unbox(v___x_904_);
v_res_912_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(v___x_28__boxed_911_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_912_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_toposortPass___closed__2(void){
_start:
{
uint8_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 2;
v___x_917_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__3(void){
_start:
{
uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___f_920_; 
v___x_918_ = lean_uint8_once(&l_Lean_Compiler_LCNF_toposortPass___closed__2, &l_Lean_Compiler_LCNF_toposortPass___closed__2_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__2);
v___x_919_ = lean_box(v___x_918_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed), 7, 1);
lean_closure_set(v___f_920_, 0, v___x_919_);
return v___f_920_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass___closed__4(void){
_start:
{
lean_object* v___f_921_; lean_object* v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___f_921_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__3, &l_Lean_Compiler_LCNF_toposortPass___closed__3_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__3);
v___x_922_ = ((lean_object*)(l_Lean_Compiler_LCNF_toposortPass___closed__1));
v___x_923_ = 0;
v___x_924_ = 2;
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_922_);
lean_ctor_set(v___x_926_, 2, v___f_921_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*3, v___x_924_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*3 + 1, v___x_924_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*3 + 2, v___x_923_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toposortPass(void){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_obj_once(&l_Lean_Compiler_LCNF_toposortPass___closed__4, &l_Lean_Compiler_LCNF_toposortPass___closed__4_once, _init_l_Lean_Compiler_LCNF_toposortPass___closed__4);
return v___x_927_;
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
