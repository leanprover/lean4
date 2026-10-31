// Lean compiler output
// Module: Lean.ConstTrie
// Imports: public import Init.System.IO public import Init.Data.Option.BasicAux import Lean.Data.Name import Std.Data.HashMap.Basic import Std.Data.HashSet.Basic import Init.Data.Array.QSort import Init.While import Init.Omega import Init.Data.Array.Lemmas import Init.Data.Array.Monadic import Init.Data.Array.Mem
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_inner_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_inner_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedConstTrie___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedConstTrie___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedConstTrie___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedConstTrie___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedConstTrie___redArg___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedConstTrie___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedConstTrie___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstTrie___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstTrie___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedConstTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstTrie___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstTrie(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ConstTrie_0__Lean_lastPartEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_lastPartEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_prefixesOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_key_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_key_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_foldlM__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_foldlM__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_parentOf(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_parentOf___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ConstTrie_ofArrays___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstTrie_ofArrays___redArg___closed__0;
static lean_once_cell_t l_Lean_ConstTrie_ofArrays___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstTrie_ofArrays___redArg___closed__1;
static lean_once_cell_t l_Lean_ConstTrie_ofArrays___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstTrie_ofArrays___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ConstTrie_ofNames_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ConstTrie_ofNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ConstTrie_ofNames___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstTrie_ofNames___closed__0;
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofNames___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_LookupCacheImpl;
lean_object* lean_imported_consts_cache_new();
LEAN_EXPORT lean_object* l_Lean_LookupCache_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_mod_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_mod_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_merged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_merged_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_lazy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedTree_lazy_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedImportedTree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedImportedTree___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedImportedTree___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedImportedTree___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedImportedTree___redArg___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedImportedTree___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedImportedTree___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedTree___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedTree___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedImportedTree___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedTree___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedTree(lean_object*);
static const lean_ctor_object l_Lean_instInhabitedImportedConsts___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedImportedTree___redArg___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedImportedConsts___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedImportedConsts___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedImportedConsts___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedImportedConsts___redArg___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedImportedConsts___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedImportedConsts___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedConsts___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedConsts___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedImportedConsts___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedConsts___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedConsts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ImportedConsts_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ImportedConsts_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findEntry_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findEntry_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_imported_extra_consts_find_entry_core(lean_object*, lean_object*);
lean_object* lean_imported_extra_consts_find_entry_cached(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_findExtraEntryCachedImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraEntryCached_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraEntryCached_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_imported_extra_consts_find_mod_idx_cached(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_findExtraModIdxCachedImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraModIdxCached_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraModIdxCached_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_find_x3f(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg(uint64_t, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0(lean_object*, uint64_t, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__0 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__1 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__2 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__3 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__4 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__5 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__6 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__7 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__1_value),((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__2_value)}};
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__8 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__8_value),((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__3_value),((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__4_value),((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__5_value),((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__9 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__9_value),((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__7_value)}};
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__10 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__2, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__10_value)} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__11 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__12 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg___boxed__const__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg___boxed__const__1_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_ImportedConsts_collectDuplicates___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ImportedConsts_collectDuplicates___redArg___closed__0 = (const lean_object*)&l_Lean_ImportedConsts_collectDuplicates___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_mergeModuleTreesLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_mergeModuleTreesLazy(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg___closed__0 = (const lean_object*)&l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_modifyAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_modifyAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlEntriesM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlEntriesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Lean_ImportedConsts_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ImportedConsts_toArray___redArg___closed__0 = (const lean_object*)&l_Lean_ImportedConsts_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_values(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ImportedConsts_find_x3f___redArg, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__0 = (const lean_object*)&l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__1 = (const lean_object*)&l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_ConstTrie_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_ConstTrie_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 0:
{
lean_object* v_key_13_; lean_object* v_val_14_; lean_object* v___x_15_; 
v_key_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_key_13_);
v_val_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_val_14_);
lean_dec_ref_known(v_t_11_, 2);
v___x_15_ = lean_apply_2(v_k_12_, v_key_13_, v_val_14_);
return v___x_15_;
}
case 1:
{
lean_object* v_key_16_; lean_object* v_children_17_; lean_object* v___x_18_; 
v_key_16_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_key_16_);
v_children_17_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_children_17_);
lean_dec_ref_known(v_t_11_, 2);
v___x_18_ = lean_apply_2(v_k_12_, v_key_16_, v_children_17_);
return v___x_18_;
}
default: 
{
lean_object* v_key_19_; lean_object* v_val_20_; lean_object* v_children_21_; lean_object* v___x_22_; 
v_key_19_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_key_19_);
v_val_20_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_val_20_);
v_children_21_ = lean_ctor_get(v_t_11_, 2);
lean_inc_ref(v_children_21_);
lean_dec_ref_known(v_t_11_, 3);
v___x_22_ = lean_apply_3(v_k_12_, v_key_19_, v_val_20_, v_children_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorElim(lean_object* v_00_u03b1_23_, lean_object* v_motive__1_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ctorElim___boxed(lean_object* v_00_u03b1_30_, lean_object* v_motive__1_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_ConstTrie_ctorElim(v_00_u03b1_30_, v_motive__1_31_, v_ctorIdx_32_, v_t_33_, v_h_34_, v_k_35_);
lean_dec(v_ctorIdx_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_leaf_elim___redArg(lean_object* v_t_37_, lean_object* v_leaf_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_37_, v_leaf_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_leaf_elim(lean_object* v_00_u03b1_40_, lean_object* v_motive__1_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_leaf_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_42_, v_leaf_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_inner_elim___redArg(lean_object* v_t_46_, lean_object* v_inner_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_46_, v_inner_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_inner_elim(lean_object* v_00_u03b1_49_, lean_object* v_motive__1_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_inner_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_51_, v_inner_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_node_elim___redArg(lean_object* v_t_55_, lean_object* v_node_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_55_, v_node_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_node_elim(lean_object* v_00_u03b1_58_, lean_object* v_motive__1_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_node_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_ConstTrie_ctorElim___redArg(v_t_60_, v_node_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstTrie___redArg(){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__1));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstTrie___redArg___boxed(lean_object* v___dummy_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_instInhabitedConstTrie___redArg();
return v_res_72_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstTrie___closed__0(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_instInhabitedConstTrie___redArg();
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstTrie(lean_object* v_00_u03b1_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_instInhabitedConstTrie___closed__0, &l_Lean_instInhabitedConstTrie___closed__0_once, _init_l_Lean_instInhabitedConstTrie___closed__0);
return v___x_75_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ConstTrie_0__Lean_lastPartEq(lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
switch(lean_obj_tag(v_x_76_))
{
case 0:
{
if (lean_obj_tag(v_x_77_) == 0)
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
case 1:
{
if (lean_obj_tag(v_x_77_) == 1)
{
lean_object* v_str_80_; lean_object* v_str_81_; uint8_t v___x_82_; 
v_str_80_ = lean_ctor_get(v_x_76_, 1);
v_str_81_ = lean_ctor_get(v_x_77_, 1);
v___x_82_ = lean_string_dec_eq(v_str_80_, v_str_81_);
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
}
default: 
{
if (lean_obj_tag(v_x_77_) == 2)
{
lean_object* v_i_84_; lean_object* v_i_85_; uint8_t v___x_86_; 
v_i_84_ = lean_ctor_get(v_x_76_, 1);
v_i_85_ = lean_ctor_get(v_x_77_, 1);
v___x_86_ = lean_nat_dec_eq(v_i_84_, v_i_85_);
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_lastPartEq___boxed(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l___private_Lean_ConstTrie_0__Lean_lastPartEq(v_x_88_, v_x_89_);
lean_dec(v_x_89_);
lean_dec(v_x_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg(lean_object* v_inst_92_, lean_object* v_cs_93_, lean_object* v_keyOf_94_, uint64_t v_h_95_, lean_object* v_lo_96_, lean_object* v_hi_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = lean_nat_dec_lt(v_lo_96_, v_hi_97_);
if (v___x_98_ == 0)
{
lean_dec(v_hi_97_);
lean_dec_ref(v_keyOf_94_);
return v_lo_96_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_mid_101_; uint64_t v___y_103_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_99_ = lean_nat_add(v_lo_96_, v_hi_97_);
v___x_100_ = lean_unsigned_to_nat(1u);
v_mid_101_ = lean_nat_shiftr(v___x_99_, v___x_100_);
lean_dec(v___x_99_);
v___x_108_ = lean_array_get_borrowed(v_inst_92_, v_cs_93_, v_mid_101_);
lean_inc_ref(v_keyOf_94_);
lean_inc(v___x_108_);
v___x_109_ = lean_apply_1(v_keyOf_94_, v___x_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
uint64_t v___x_110_; 
v___x_110_ = 1723ULL;
v___y_103_ = v___x_110_;
goto v___jp_102_;
}
else
{
uint64_t v_hash_111_; 
v_hash_111_ = lean_ctor_get_uint64(v___x_109_, sizeof(void*)*2);
lean_dec(v___x_109_);
v___y_103_ = v_hash_111_;
goto v___jp_102_;
}
v___jp_102_:
{
uint8_t v___x_104_; 
v___x_104_ = lean_uint64_dec_lt(v___y_103_, v_h_95_);
if (v___x_104_ == 0)
{
lean_dec(v_hi_97_);
v_hi_97_ = v_mid_101_;
goto _start;
}
else
{
lean_object* v___x_106_; 
lean_dec(v_lo_96_);
v___x_106_ = lean_nat_add(v_mid_101_, v___x_100_);
lean_dec(v_mid_101_);
v_lo_96_ = v___x_106_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg___boxed(lean_object* v_inst_112_, lean_object* v_cs_113_, lean_object* v_keyOf_114_, lean_object* v_h_115_, lean_object* v_lo_116_, lean_object* v_hi_117_){
_start:
{
uint64_t v_h_boxed_118_; lean_object* v_res_119_; 
v_h_boxed_118_ = lean_unbox_uint64(v_h_115_);
lean_dec_ref(v_h_115_);
v_res_119_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg(v_inst_112_, v_cs_113_, v_keyOf_114_, v_h_boxed_118_, v_lo_116_, v_hi_117_);
lean_dec_ref(v_cs_113_);
lean_dec(v_inst_112_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound(lean_object* v_00_u03b2_120_, lean_object* v_inst_121_, lean_object* v_cs_122_, lean_object* v_keyOf_123_, uint64_t v_h_124_, lean_object* v_lo_125_, lean_object* v_hi_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg(v_inst_121_, v_cs_122_, v_keyOf_123_, v_h_124_, v_lo_125_, v_hi_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___boxed(lean_object* v_00_u03b2_128_, lean_object* v_inst_129_, lean_object* v_cs_130_, lean_object* v_keyOf_131_, lean_object* v_h_132_, lean_object* v_lo_133_, lean_object* v_hi_134_){
_start:
{
uint64_t v_h_boxed_135_; lean_object* v_res_136_; 
v_h_boxed_135_ = lean_unbox_uint64(v_h_132_);
lean_dec_ref(v_h_132_);
v_res_136_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound(v_00_u03b2_128_, v_inst_129_, v_cs_130_, v_keyOf_131_, v_h_boxed_135_, v_lo_133_, v_hi_134_);
lean_dec_ref(v_cs_130_);
lean_dec(v_inst_129_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg(lean_object* v_inst_137_, lean_object* v_cs_138_, lean_object* v_keyOf_139_, lean_object* v_k_140_, uint64_t v_h_141_, lean_object* v_j_142_){
_start:
{
uint8_t v___y_148_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_array_get_size(v_cs_138_);
v___x_151_ = lean_nat_dec_lt(v_j_142_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_j_142_);
lean_dec_ref(v_keyOf_139_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v_c_154_; uint64_t v___y_156_; 
v___x_153_ = lean_array_get_borrowed(v_inst_137_, v_cs_138_, v_j_142_);
lean_inc_ref(v_keyOf_139_);
lean_inc(v___x_153_);
v_c_154_ = lean_apply_1(v_keyOf_139_, v___x_153_);
if (lean_obj_tag(v_c_154_) == 0)
{
uint64_t v___x_166_; 
v___x_166_ = 1723ULL;
v___y_156_ = v___x_166_;
goto v___jp_155_;
}
else
{
uint64_t v_hash_167_; 
v_hash_167_ = lean_ctor_get_uint64(v_c_154_, sizeof(void*)*2);
v___y_156_ = v_hash_167_;
goto v___jp_155_;
}
v___jp_155_:
{
uint8_t v___x_157_; 
v___x_157_ = lean_uint64_dec_eq(v___y_156_, v_h_141_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_dec(v_c_154_);
lean_dec(v_j_142_);
lean_dec_ref(v_keyOf_139_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
switch(lean_obj_tag(v_c_154_))
{
case 0:
{
if (lean_obj_tag(v_k_140_) == 0)
{
lean_object* v___x_159_; 
lean_dec_ref(v_keyOf_139_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v_j_142_);
return v___x_159_;
}
else
{
goto v___jp_143_;
}
}
case 1:
{
if (lean_obj_tag(v_k_140_) == 1)
{
lean_object* v_str_160_; lean_object* v_str_161_; uint8_t v___x_162_; 
v_str_160_ = lean_ctor_get(v_c_154_, 1);
lean_inc_ref(v_str_160_);
lean_dec_ref_known(v_c_154_, 2);
v_str_161_ = lean_ctor_get(v_k_140_, 1);
v___x_162_ = lean_string_dec_eq(v_str_160_, v_str_161_);
lean_dec_ref(v_str_160_);
v___y_148_ = v___x_162_;
goto v___jp_147_;
}
else
{
lean_dec_ref_known(v_c_154_, 2);
goto v___jp_143_;
}
}
default: 
{
if (lean_obj_tag(v_k_140_) == 2)
{
lean_object* v_i_163_; lean_object* v_i_164_; uint8_t v___x_165_; 
v_i_163_ = lean_ctor_get(v_c_154_, 1);
lean_inc(v_i_163_);
lean_dec_ref_known(v_c_154_, 2);
v_i_164_ = lean_ctor_get(v_k_140_, 1);
v___x_165_ = lean_nat_dec_eq(v_i_163_, v_i_164_);
lean_dec(v_i_163_);
v___y_148_ = v___x_165_;
goto v___jp_147_;
}
else
{
lean_dec_ref_known(v_c_154_, 2);
goto v___jp_143_;
}
}
}
}
}
}
v___jp_143_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_add(v_j_142_, v___x_144_);
lean_dec(v_j_142_);
v_j_142_ = v___x_145_;
goto _start;
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
goto v___jp_143_;
}
else
{
lean_object* v___x_149_; 
lean_dec_ref(v_keyOf_139_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v_j_142_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg___boxed(lean_object* v_inst_168_, lean_object* v_cs_169_, lean_object* v_keyOf_170_, lean_object* v_k_171_, lean_object* v_h_172_, lean_object* v_j_173_){
_start:
{
uint64_t v_h_boxed_174_; lean_object* v_res_175_; 
v_h_boxed_174_ = lean_unbox_uint64(v_h_172_);
lean_dec_ref(v_h_172_);
v_res_175_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg(v_inst_168_, v_cs_169_, v_keyOf_170_, v_k_171_, v_h_boxed_174_, v_j_173_);
lean_dec(v_k_171_);
lean_dec_ref(v_cs_169_);
lean_dec(v_inst_168_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun(lean_object* v_00_u03b2_176_, lean_object* v_inst_177_, lean_object* v_cs_178_, lean_object* v_keyOf_179_, lean_object* v_k_180_, uint64_t v_h_181_, lean_object* v_j_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg(v_inst_177_, v_cs_178_, v_keyOf_179_, v_k_180_, v_h_181_, v_j_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___boxed(lean_object* v_00_u03b2_184_, lean_object* v_inst_185_, lean_object* v_cs_186_, lean_object* v_keyOf_187_, lean_object* v_k_188_, lean_object* v_h_189_, lean_object* v_j_190_){
_start:
{
uint64_t v_h_boxed_191_; lean_object* v_res_192_; 
v_h_boxed_191_ = lean_unbox_uint64(v_h_189_);
lean_dec_ref(v_h_189_);
v_res_192_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun(v_00_u03b2_184_, v_inst_185_, v_cs_186_, v_keyOf_187_, v_k_188_, v_h_boxed_191_, v_j_190_);
lean_dec(v_k_188_);
lean_dec_ref(v_cs_186_);
lean_dec(v_inst_185_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg(lean_object* v_inst_193_, lean_object* v_cs_194_, lean_object* v_keyOf_195_, lean_object* v_k_196_){
_start:
{
uint64_t v___y_198_; 
if (lean_obj_tag(v_k_196_) == 0)
{
uint64_t v___x_203_; 
v___x_203_ = 1723ULL;
v___y_198_ = v___x_203_;
goto v___jp_197_;
}
else
{
uint64_t v_hash_204_; 
v_hash_204_ = lean_ctor_get_uint64(v_k_196_, sizeof(void*)*2);
v___y_198_ = v_hash_204_;
goto v___jp_197_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_array_get_size(v_cs_194_);
lean_inc_ref(v_keyOf_195_);
v___x_201_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___redArg(v_inst_193_, v_cs_194_, v_keyOf_195_, v___y_198_, v___x_199_, v___x_200_);
v___x_202_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___redArg(v_inst_193_, v_cs_194_, v_keyOf_195_, v_k_196_, v___y_198_, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg___boxed(lean_object* v_inst_205_, lean_object* v_cs_206_, lean_object* v_keyOf_207_, lean_object* v_k_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg(v_inst_205_, v_cs_206_, v_keyOf_207_, v_k_208_);
lean_dec(v_k_208_);
lean_dec_ref(v_cs_206_);
lean_dec(v_inst_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f(lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_cs_212_, lean_object* v_keyOf_213_, lean_object* v_k_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg(v_inst_211_, v_cs_212_, v_keyOf_213_, v_k_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___boxed(lean_object* v_00_u03b2_216_, lean_object* v_inst_217_, lean_object* v_cs_218_, lean_object* v_keyOf_219_, lean_object* v_k_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f(v_00_u03b2_216_, v_inst_217_, v_cs_218_, v_keyOf_219_, v_k_220_);
lean_dec(v_k_220_);
lean_dec_ref(v_cs_218_);
lean_dec(v_inst_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_prefixesOf(lean_object* v_n_222_, lean_object* v_acc_223_){
_start:
{
if (lean_obj_tag(v_n_222_) == 0)
{
return v_acc_223_;
}
else
{
lean_object* v_pre_224_; lean_object* v___x_225_; 
v_pre_224_ = lean_ctor_get(v_n_222_, 0);
lean_inc(v_pre_224_);
v___x_225_ = lean_array_push(v_acc_223_, v_n_222_);
v_n_222_ = v_pre_224_;
v_acc_223_ = v___x_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key___redArg(lean_object* v_x_227_){
_start:
{
lean_object* v_key_228_; 
v_key_228_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_key_228_);
return v_key_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key___redArg___boxed(lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_ConstTrie_key___redArg(v_x_229_);
lean_dec_ref(v_x_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key(lean_object* v_00_u03b1_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_key_233_; 
v_key_233_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_key_233_);
return v_key_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_key___boxed(lean_object* v_00_u03b1_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_ConstTrie_key(v_00_u03b1_234_, v_x_235_);
lean_dec_ref(v_x_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f___redArg(lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 1)
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_240_; 
v_val_239_ = lean_ctor_get(v_x_237_, 1);
lean_inc(v_val_239_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_val_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f___redArg___boxed(lean_object* v_x_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_ConstTrie_val_x3f___redArg(v_x_241_);
lean_dec_ref(v_x_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f(lean_object* v_00_u03b1_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 1)
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(0);
return v___x_245_;
}
else
{
lean_object* v_val_246_; lean_object* v___x_247_; 
v_val_246_ = lean_ctor_get(v_x_244_, 1);
lean_inc(v_val_246_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_val_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_val_x3f___boxed(lean_object* v_00_u03b1_248_, lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_ConstTrie_val_x3f(v_00_u03b1_248_, v_x_249_);
lean_dec_ref(v_x_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children___redArg(lean_object* v_x_251_){
_start:
{
switch(lean_obj_tag(v_x_251_))
{
case 0:
{
lean_object* v___x_252_; 
v___x_252_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
return v___x_252_;
}
case 1:
{
lean_object* v_children_253_; 
v_children_253_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_children_253_);
return v_children_253_;
}
default: 
{
lean_object* v_children_254_; 
v_children_254_ = lean_ctor_get(v_x_251_, 2);
lean_inc_ref(v_children_254_);
return v_children_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children___redArg___boxed(lean_object* v_x_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_ConstTrie_children___redArg(v_x_255_);
lean_dec_ref(v_x_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children(lean_object* v_00_u03b1_257_, lean_object* v_x_258_){
_start:
{
switch(lean_obj_tag(v_x_258_))
{
case 0:
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
return v___x_259_;
}
case 1:
{
lean_object* v_children_260_; 
v_children_260_ = lean_ctor_get(v_x_258_, 1);
lean_inc_ref(v_children_260_);
return v_children_260_;
}
default: 
{
lean_object* v_children_261_; 
v_children_261_ = lean_ctor_get(v_x_258_, 2);
lean_inc_ref(v_children_261_);
return v_children_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_children___boxed(lean_object* v_00_u03b1_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_ConstTrie_children(v_00_u03b1_262_, v_x_263_);
lean_dec_ref(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk___redArg(lean_object* v_key_265_, lean_object* v_val_x3f_266_, lean_object* v_children_267_){
_start:
{
if (lean_obj_tag(v_val_x3f_266_) == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v_key_265_);
lean_ctor_set(v___x_268_, 1, v_children_267_);
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_val_269_ = lean_ctor_get(v_val_x3f_266_, 0);
v___x_270_ = lean_array_get_size(v_children_267_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_inc(v_val_269_);
v___x_273_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_273_, 0, v_key_265_);
lean_ctor_set(v___x_273_, 1, v_val_269_);
lean_ctor_set(v___x_273_, 2, v_children_267_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v_children_267_);
lean_inc(v_val_269_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_key_265_);
lean_ctor_set(v___x_274_, 1, v_val_269_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk___redArg___boxed(lean_object* v_key_275_, lean_object* v_val_x3f_276_, lean_object* v_children_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_ConstTrie_mk___redArg(v_key_275_, v_val_x3f_276_, v_children_277_);
lean_dec(v_val_x3f_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk(lean_object* v_00_u03b1_279_, lean_object* v_key_280_, lean_object* v_val_x3f_281_, lean_object* v_children_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_ConstTrie_mk___redArg(v_key_280_, v_val_x3f_281_, v_children_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_mk___boxed(lean_object* v_00_u03b1_284_, lean_object* v_key_285_, lean_object* v_val_x3f_286_, lean_object* v_children_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_ConstTrie_mk(v_00_u03b1_284_, v_key_285_, v_val_x3f_286_, v_children_287_);
lean_dec(v_val_x3f_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg(lean_object* v_cs_289_, uint64_t v_h_290_, lean_object* v_lo_291_, lean_object* v_hi_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = lean_nat_dec_lt(v_lo_291_, v_hi_292_);
if (v___x_293_ == 0)
{
lean_dec(v_hi_292_);
return v_lo_291_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_mid_297_; uint64_t v___y_299_; lean_object* v___y_305_; lean_object* v___x_308_; lean_object* v_key_309_; 
v___x_294_ = lean_obj_once(&l_Lean_instInhabitedConstTrie___closed__0, &l_Lean_instInhabitedConstTrie___closed__0_once, _init_l_Lean_instInhabitedConstTrie___closed__0);
v___x_295_ = lean_nat_add(v_lo_291_, v_hi_292_);
v___x_296_ = lean_unsigned_to_nat(1u);
v_mid_297_ = lean_nat_shiftr(v___x_295_, v___x_296_);
lean_dec(v___x_295_);
v___x_308_ = lean_array_get_borrowed(v___x_294_, v_cs_289_, v_mid_297_);
v_key_309_ = lean_ctor_get(v___x_308_, 0);
v___y_305_ = v_key_309_;
goto v___jp_304_;
v___jp_298_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_uint64_dec_lt(v___y_299_, v_h_290_);
if (v___x_300_ == 0)
{
lean_dec(v_hi_292_);
v_hi_292_ = v_mid_297_;
goto _start;
}
else
{
lean_object* v___x_302_; 
lean_dec(v_lo_291_);
v___x_302_ = lean_nat_add(v_mid_297_, v___x_296_);
lean_dec(v_mid_297_);
v_lo_291_ = v___x_302_;
goto _start;
}
}
v___jp_304_:
{
if (lean_obj_tag(v___y_305_) == 0)
{
uint64_t v___x_306_; 
v___x_306_ = 1723ULL;
v___y_299_ = v___x_306_;
goto v___jp_298_;
}
else
{
uint64_t v_hash_307_; 
v_hash_307_ = lean_ctor_get_uint64(v___y_305_, sizeof(void*)*2);
v___y_299_ = v_hash_307_;
goto v___jp_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg___boxed(lean_object* v_cs_310_, lean_object* v_h_311_, lean_object* v_lo_312_, lean_object* v_hi_313_){
_start:
{
uint64_t v_h_boxed_314_; lean_object* v_res_315_; 
v_h_boxed_314_ = lean_unbox_uint64(v_h_311_);
lean_dec_ref(v_h_311_);
v_res_315_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg(v_cs_310_, v_h_boxed_314_, v_lo_312_, v_hi_313_);
lean_dec_ref(v_cs_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg(lean_object* v_cs_316_, lean_object* v_k_317_, uint64_t v_h_318_, lean_object* v_j_319_){
_start:
{
uint8_t v___y_325_; lean_object* v___y_328_; uint64_t v___y_329_; lean_object* v___y_340_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_array_get_size(v_cs_316_);
v___x_344_ = lean_nat_dec_lt(v_j_319_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec(v_j_319_);
v___x_345_ = lean_box(0);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_key_348_; 
v___x_346_ = lean_obj_once(&l_Lean_instInhabitedConstTrie___closed__0, &l_Lean_instInhabitedConstTrie___closed__0_once, _init_l_Lean_instInhabitedConstTrie___closed__0);
v___x_347_ = lean_array_get_borrowed(v___x_346_, v_cs_316_, v_j_319_);
v_key_348_ = lean_ctor_get(v___x_347_, 0);
v___y_340_ = v_key_348_;
goto v___jp_339_;
}
v___jp_320_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_j_319_, v___x_321_);
lean_dec(v_j_319_);
v_j_319_ = v___x_322_;
goto _start;
}
v___jp_324_:
{
if (v___y_325_ == 0)
{
goto v___jp_320_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_j_319_);
return v___x_326_;
}
}
v___jp_327_:
{
uint8_t v___x_330_; 
v___x_330_ = lean_uint64_dec_eq(v___y_329_, v_h_318_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_j_319_);
v___x_331_ = lean_box(0);
return v___x_331_;
}
else
{
switch(lean_obj_tag(v___y_328_))
{
case 0:
{
if (lean_obj_tag(v_k_317_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v_j_319_);
return v___x_332_;
}
else
{
goto v___jp_320_;
}
}
case 1:
{
if (lean_obj_tag(v_k_317_) == 1)
{
lean_object* v_str_333_; lean_object* v_str_334_; uint8_t v___x_335_; 
v_str_333_ = lean_ctor_get(v___y_328_, 1);
v_str_334_ = lean_ctor_get(v_k_317_, 1);
v___x_335_ = lean_string_dec_eq(v_str_333_, v_str_334_);
v___y_325_ = v___x_335_;
goto v___jp_324_;
}
else
{
goto v___jp_320_;
}
}
default: 
{
if (lean_obj_tag(v_k_317_) == 2)
{
lean_object* v_i_336_; lean_object* v_i_337_; uint8_t v___x_338_; 
v_i_336_ = lean_ctor_get(v___y_328_, 1);
v_i_337_ = lean_ctor_get(v_k_317_, 1);
v___x_338_ = lean_nat_dec_eq(v_i_336_, v_i_337_);
v___y_325_ = v___x_338_;
goto v___jp_324_;
}
else
{
goto v___jp_320_;
}
}
}
}
}
v___jp_339_:
{
if (lean_obj_tag(v___y_340_) == 0)
{
uint64_t v___x_341_; 
v___x_341_ = 1723ULL;
v___y_328_ = v___y_340_;
v___y_329_ = v___x_341_;
goto v___jp_327_;
}
else
{
uint64_t v_hash_342_; 
v_hash_342_ = lean_ctor_get_uint64(v___y_340_, sizeof(void*)*2);
v___y_328_ = v___y_340_;
v___y_329_ = v_hash_342_;
goto v___jp_327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg___boxed(lean_object* v_cs_349_, lean_object* v_k_350_, lean_object* v_h_351_, lean_object* v_j_352_){
_start:
{
uint64_t v_h_boxed_353_; lean_object* v_res_354_; 
v_h_boxed_353_ = lean_unbox_uint64(v_h_351_);
lean_dec_ref(v_h_351_);
v_res_354_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg(v_cs_349_, v_k_350_, v_h_boxed_353_, v_j_352_);
lean_dec(v_k_350_);
lean_dec_ref(v_cs_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg(lean_object* v_cs_355_, lean_object* v_k_356_){
_start:
{
uint64_t v___y_358_; 
if (lean_obj_tag(v_k_356_) == 0)
{
uint64_t v___x_363_; 
v___x_363_ = 1723ULL;
v___y_358_ = v___x_363_;
goto v___jp_357_;
}
else
{
uint64_t v_hash_364_; 
v_hash_364_ = lean_ctor_get_uint64(v_k_356_, sizeof(void*)*2);
v___y_358_ = v_hash_364_;
goto v___jp_357_;
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v_cs_355_);
v___x_361_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg(v_cs_355_, v___y_358_, v___x_359_, v___x_360_);
v___x_362_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg(v_cs_355_, v_k_356_, v___y_358_, v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg___boxed(lean_object* v_cs_365_, lean_object* v_k_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg(v_cs_365_, v_k_366_);
lean_dec(v_k_366_);
lean_dec_ref(v_cs_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(lean_object* v_t_368_, lean_object* v_path_369_, lean_object* v_i_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_cs_374_; 
v___x_371_ = lean_box(0);
v___x_372_ = lean_obj_once(&l_Lean_instInhabitedConstTrie___closed__0, &l_Lean_instInhabitedConstTrie___closed__0_once, _init_l_Lean_instInhabitedConstTrie___closed__0);
switch(lean_obj_tag(v_t_368_))
{
case 0:
{
lean_object* v_val_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_val_383_ = lean_ctor_get(v_t_368_, 1);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_nat_dec_eq(v_i_370_, v___x_384_);
lean_dec(v_i_370_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
lean_inc(v_val_383_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v_val_383_);
return v___x_387_;
}
}
case 1:
{
lean_object* v_children_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_children_388_ = lean_ctor_get(v_t_368_, 1);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_nat_dec_eq(v_i_370_, v___x_389_);
if (v___x_390_ == 0)
{
v_cs_374_ = v_children_388_;
goto v___jp_373_;
}
else
{
lean_object* v___x_391_; 
lean_dec(v_i_370_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
default: 
{
lean_object* v_val_392_; lean_object* v_children_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_val_392_ = lean_ctor_get(v_t_368_, 1);
v_children_393_ = lean_ctor_get(v_t_368_, 2);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_nat_dec_eq(v_i_370_, v___x_394_);
if (v___x_395_ == 0)
{
v_cs_374_ = v_children_393_;
goto v___jp_373_;
}
else
{
lean_object* v___x_396_; 
lean_dec(v_i_370_);
lean_inc(v_val_392_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_val_392_);
return v___x_396_;
}
}
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_sub(v_i_370_, v___x_375_);
lean_dec(v_i_370_);
v___x_377_ = lean_array_get_borrowed(v___x_371_, v_path_369_, v___x_376_);
v___x_378_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg(v_cs_374_, v___x_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_379_; 
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v___x_381_; 
v_val_380_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v___x_378_, 1);
v___x_381_ = lean_array_get_borrowed(v___x_372_, v_cs_374_, v_val_380_);
lean_dec(v_val_380_);
v_t_368_ = v___x_381_;
v_i_370_ = v___x_376_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg___boxed(lean_object* v_t_397_, lean_object* v_path_398_, lean_object* v_i_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(v_t_397_, v_path_398_, v_i_399_);
lean_dec_ref(v_path_398_);
lean_dec_ref(v_t_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux(lean_object* v_00_u03b1_401_, lean_object* v_t_402_, lean_object* v_path_403_, lean_object* v_i_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(v_t_402_, v_path_403_, v_i_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___boxed(lean_object* v_00_u03b1_406_, lean_object* v_t_407_, lean_object* v_path_408_, lean_object* v_i_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux(v_00_u03b1_406_, v_t_407_, v_path_408_, v_i_409_);
lean_dec_ref(v_path_408_);
lean_dec_ref(v_t_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0(lean_object* v_00_u03b1_411_, lean_object* v_cs_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___redArg(v_cs_412_, v_k_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0___boxed(lean_object* v_00_u03b1_415_, lean_object* v_cs_416_, lean_object* v_k_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0(v_00_u03b1_415_, v_cs_416_, v_k_417_);
lean_dec(v_k_417_);
lean_dec_ref(v_cs_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0(lean_object* v_00_u03b1_419_, lean_object* v_cs_420_, uint64_t v_h_421_, lean_object* v_lo_422_, lean_object* v_hi_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___redArg(v_cs_420_, v_h_421_, v_lo_422_, v_hi_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0___boxed(lean_object* v_00_u03b1_425_, lean_object* v_cs_426_, lean_object* v_h_427_, lean_object* v_lo_428_, lean_object* v_hi_429_){
_start:
{
uint64_t v_h_boxed_430_; lean_object* v_res_431_; 
v_h_boxed_430_ = lean_unbox_uint64(v_h_427_);
lean_dec_ref(v_h_427_);
v_res_431_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__0(v_00_u03b1_425_, v_cs_426_, v_h_boxed_430_, v_lo_428_, v_hi_429_);
lean_dec_ref(v_cs_426_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1(lean_object* v_00_u03b1_432_, lean_object* v_cs_433_, lean_object* v_k_434_, uint64_t v_h_435_, lean_object* v_j_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___redArg(v_cs_433_, v_k_434_, v_h_435_, v_j_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1___boxed(lean_object* v_00_u03b1_438_, lean_object* v_cs_439_, lean_object* v_k_440_, lean_object* v_h_441_, lean_object* v_j_442_){
_start:
{
uint64_t v_h_boxed_443_; lean_object* v_res_444_; 
v_h_boxed_443_ = lean_unbox_uint64(v_h_441_);
lean_dec_ref(v_h_441_);
v_res_444_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_spec__0_spec__1(v_00_u03b1_438_, v_cs_439_, v_k_440_, v_h_boxed_443_, v_j_442_);
lean_dec(v_k_440_);
lean_dec_ref(v_cs_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_key_match__1_splitter___redArg(lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_, lean_object* v_h__3_448_){
_start:
{
switch(lean_obj_tag(v_x_445_))
{
case 0:
{
lean_object* v_key_449_; lean_object* v_val_450_; lean_object* v___x_451_; 
lean_dec(v_h__3_448_);
lean_dec(v_h__2_447_);
v_key_449_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_key_449_);
v_val_450_ = lean_ctor_get(v_x_445_, 1);
lean_inc(v_val_450_);
lean_dec_ref_known(v_x_445_, 2);
v___x_451_ = lean_apply_2(v_h__1_446_, v_key_449_, v_val_450_);
return v___x_451_;
}
case 1:
{
lean_object* v_key_452_; lean_object* v_children_453_; lean_object* v___x_454_; 
lean_dec(v_h__3_448_);
lean_dec(v_h__1_446_);
v_key_452_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_key_452_);
v_children_453_ = lean_ctor_get(v_x_445_, 1);
lean_inc_ref(v_children_453_);
lean_dec_ref_known(v_x_445_, 2);
v___x_454_ = lean_apply_2(v_h__2_447_, v_key_452_, v_children_453_);
return v___x_454_;
}
default: 
{
lean_object* v_key_455_; lean_object* v_val_456_; lean_object* v_children_457_; lean_object* v___x_458_; 
lean_dec(v_h__2_447_);
lean_dec(v_h__1_446_);
v_key_455_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_key_455_);
v_val_456_ = lean_ctor_get(v_x_445_, 1);
lean_inc(v_val_456_);
v_children_457_ = lean_ctor_get(v_x_445_, 2);
lean_inc_ref(v_children_457_);
lean_dec_ref_known(v_x_445_, 3);
v___x_458_ = lean_apply_3(v_h__3_448_, v_key_455_, v_val_456_, v_children_457_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_key_match__1_splitter(lean_object* v_00_u03b1_459_, lean_object* v_motive_460_, lean_object* v_x_461_, lean_object* v_h__1_462_, lean_object* v_h__2_463_, lean_object* v_h__3_464_){
_start:
{
switch(lean_obj_tag(v_x_461_))
{
case 0:
{
lean_object* v_key_465_; lean_object* v_val_466_; lean_object* v___x_467_; 
lean_dec(v_h__3_464_);
lean_dec(v_h__2_463_);
v_key_465_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_key_465_);
v_val_466_ = lean_ctor_get(v_x_461_, 1);
lean_inc(v_val_466_);
lean_dec_ref_known(v_x_461_, 2);
v___x_467_ = lean_apply_2(v_h__1_462_, v_key_465_, v_val_466_);
return v___x_467_;
}
case 1:
{
lean_object* v_key_468_; lean_object* v_children_469_; lean_object* v___x_470_; 
lean_dec(v_h__3_464_);
lean_dec(v_h__1_462_);
v_key_468_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_key_468_);
v_children_469_ = lean_ctor_get(v_x_461_, 1);
lean_inc_ref(v_children_469_);
lean_dec_ref_known(v_x_461_, 2);
v___x_470_ = lean_apply_2(v_h__2_463_, v_key_468_, v_children_469_);
return v___x_470_;
}
default: 
{
lean_object* v_key_471_; lean_object* v_val_472_; lean_object* v_children_473_; lean_object* v___x_474_; 
lean_dec(v_h__2_463_);
lean_dec(v_h__1_462_);
v_key_471_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_key_471_);
v_val_472_ = lean_ctor_get(v_x_461_, 1);
lean_inc(v_val_472_);
v_children_473_ = lean_ctor_get(v_x_461_, 2);
lean_inc_ref(v_children_473_);
lean_dec_ref_known(v_x_461_, 3);
v___x_474_ = lean_apply_3(v_h__3_464_, v_key_471_, v_val_472_, v_children_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_match__1_splitter___redArg(lean_object* v_x_475_, lean_object* v_h__1_476_, lean_object* v_h__2_477_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_h__1_476_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_apply_1(v_h__2_477_, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; 
lean_dec(v_h__2_477_);
v_val_480_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v_x_475_, 1);
v___x_481_ = lean_apply_1(v_h__1_476_, v_val_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux_match__1_splitter(lean_object* v_motive_482_, lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_h__1_484_);
v___x_486_ = lean_box(0);
v___x_487_ = lean_apply_1(v_h__2_485_, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_489_; 
lean_dec(v_h__2_485_);
v_val_488_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_x_483_, 1);
v___x_489_ = lean_apply_1(v_h__1_484_, v_val_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f___redArg(lean_object* v_t_490_, lean_object* v_n_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_path_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = lean_unsigned_to_nat(8u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v_path_494_ = l___private_Lean_ConstTrie_0__Lean_prefixesOf(v_n_491_, v___x_493_);
v___x_495_ = lean_array_get_size(v_path_494_);
v___x_496_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(v_t_490_, v_path_494_, v___x_495_);
lean_dec_ref(v_path_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f___redArg___boxed(lean_object* v_t_497_, lean_object* v_n_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_ConstTrie_find_x3f___redArg(v_t_497_, v_n_498_);
lean_dec_ref(v_t_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f(lean_object* v_00_u03b1_500_, lean_object* v_t_501_, lean_object* v_n_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_ConstTrie_find_x3f___redArg(v_t_501_, v_n_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_find_x3f___boxed(lean_object* v_00_u03b1_504_, lean_object* v_t_505_, lean_object* v_n_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_ConstTrie_find_x3f(v_00_u03b1_504_, v_t_505_, v_n_506_);
lean_dec_ref(v_t_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___redArg___lam__2(lean_object* v_toApplicative_508_, lean_object* v_children_509_, lean_object* v_inst_510_, lean_object* v___f_511_, lean_object* v_____do__lift_512_){
_start:
{
lean_object* v_toPure_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_toPure_513_ = lean_ctor_get(v_toApplicative_508_, 1);
lean_inc(v_toPure_513_);
lean_dec_ref(v_toApplicative_508_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_array_get_size(v_children_509_);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v___f_511_);
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_children_509_);
v___x_517_ = lean_apply_2(v_toPure_513_, lean_box(0), v_____do__lift_512_);
return v___x_517_;
}
else
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
lean_dec(v_toPure_513_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = lean_usize_of_nat(v___x_515_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_510_, v___f_511_, v_children_509_, v___x_518_, v___x_519_, v_____do__lift_512_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___redArg(lean_object* v_inst_521_, lean_object* v_t_522_, lean_object* v_f_523_, lean_object* v_init_524_){
_start:
{
switch(lean_obj_tag(v_t_522_))
{
case 0:
{
lean_object* v_key_525_; lean_object* v_val_526_; lean_object* v___x_527_; 
lean_dec_ref(v_inst_521_);
v_key_525_ = lean_ctor_get(v_t_522_, 0);
lean_inc(v_key_525_);
v_val_526_ = lean_ctor_get(v_t_522_, 1);
lean_inc(v_val_526_);
lean_dec_ref_known(v_t_522_, 2);
v___x_527_ = lean_apply_3(v_f_523_, v_init_524_, v_key_525_, v_val_526_);
return v___x_527_;
}
case 1:
{
lean_object* v_toApplicative_528_; lean_object* v_children_529_; lean_object* v_toPure_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_toApplicative_528_ = lean_ctor_get(v_inst_521_, 0);
v_children_529_ = lean_ctor_get(v_t_522_, 1);
lean_inc_ref(v_children_529_);
lean_dec_ref_known(v_t_522_, 2);
v_toPure_530_ = lean_ctor_get(v_toApplicative_528_, 1);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_children_529_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_inc(v_toPure_530_);
lean_dec_ref(v_children_529_);
lean_dec(v_f_523_);
lean_dec_ref(v_inst_521_);
v___x_534_ = lean_apply_2(v_toPure_530_, lean_box(0), v_init_524_);
return v___x_534_;
}
else
{
lean_object* v___f_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
lean_inc_ref(v_inst_521_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_ConstTrie_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_535_, 0, v_inst_521_);
lean_closure_set(v___f_535_, 1, v_f_523_);
v___x_536_ = ((size_t)0ULL);
v___x_537_ = lean_usize_of_nat(v___x_532_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_521_, v___f_535_, v_children_529_, v___x_536_, v___x_537_, v_init_524_);
return v___x_538_;
}
}
default: 
{
lean_object* v_toApplicative_539_; lean_object* v_toBind_540_; lean_object* v_key_541_; lean_object* v_val_542_; lean_object* v_children_543_; lean_object* v___f_544_; lean_object* v___f_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_toApplicative_539_ = lean_ctor_get(v_inst_521_, 0);
lean_inc_ref(v_toApplicative_539_);
v_toBind_540_ = lean_ctor_get(v_inst_521_, 1);
lean_inc(v_toBind_540_);
v_key_541_ = lean_ctor_get(v_t_522_, 0);
lean_inc(v_key_541_);
v_val_542_ = lean_ctor_get(v_t_522_, 1);
lean_inc(v_val_542_);
v_children_543_ = lean_ctor_get(v_t_522_, 2);
lean_inc_ref(v_children_543_);
lean_dec_ref_known(v_t_522_, 3);
lean_inc(v_f_523_);
lean_inc_ref(v_inst_521_);
v___f_544_ = lean_alloc_closure((void*)(l_Lean_ConstTrie_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_544_, 0, v_inst_521_);
lean_closure_set(v___f_544_, 1, v_f_523_);
v___f_545_ = lean_alloc_closure((void*)(l_Lean_ConstTrie_foldlM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_545_, 0, v_toApplicative_539_);
lean_closure_set(v___f_545_, 1, v_children_543_);
lean_closure_set(v___f_545_, 2, v_inst_521_);
lean_closure_set(v___f_545_, 3, v___f_544_);
v___x_546_ = lean_apply_3(v_f_523_, v_init_524_, v_key_541_, v_val_542_);
v___x_547_ = lean_apply_4(v_toBind_540_, lean_box(0), lean_box(0), v___x_546_, v___f_545_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___redArg___lam__0(lean_object* v_inst_548_, lean_object* v_f_549_, lean_object* v_s_550_, lean_object* v_c_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_ConstTrie_foldlM___redArg(v_inst_548_, v_c_551_, v_f_549_, v_s_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM(lean_object* v_m_553_, lean_object* v_00_u03b1_554_, lean_object* v_00_u03c3_555_, lean_object* v_inst_556_, lean_object* v_t_557_, lean_object* v_f_558_, lean_object* v_init_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_ConstTrie_foldlM___redArg(v_inst_556_, v_t_557_, v_f_558_, v_init_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_foldlM__unattach_match__1_splitter___redArg(lean_object* v_x_561_, lean_object* v_h__1_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_2(v_h__1_562_, v_x_561_, lean_box(0));
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_foldlM__unattach_match__1_splitter(lean_object* v_00_u03b1_564_, lean_object* v_P_565_, lean_object* v_motive_566_, lean_object* v_x_567_, lean_object* v_h__1_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_apply_2(v_h__1_568_, v_x_567_, lean_box(0));
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_parentOf(lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
return v_x_570_;
}
else
{
lean_object* v_pre_571_; 
v_pre_571_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_pre_571_);
return v_pre_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_parentOf___boxed(lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_parentOf(v_x_572_);
lean_dec(v_x_572_);
return v_res_573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
uint8_t v___x_576_; 
v___x_576_ = 0;
return v___x_576_;
}
else
{
lean_object* v_key_577_; lean_object* v_tail_578_; uint8_t v___x_579_; 
v_key_577_ = lean_ctor_get(v_x_575_, 0);
v_tail_578_ = lean_ctor_get(v_x_575_, 2);
v___x_579_ = lean_name_eq(v_key_577_, v_a_574_);
if (v___x_579_ == 0)
{
v_x_575_ = v_tail_578_;
goto _start;
}
else
{
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg___boxed(lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec(v_a_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg(lean_object* v_m_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_buckets_587_; lean_object* v___x_588_; uint64_t v___y_590_; 
v_buckets_587_ = lean_ctor_get(v_m_585_, 1);
v___x_588_ = lean_array_get_size(v_buckets_587_);
if (lean_obj_tag(v_a_586_) == 0)
{
uint64_t v___x_604_; 
v___x_604_ = 1723ULL;
v___y_590_ = v___x_604_;
goto v___jp_589_;
}
else
{
uint64_t v_hash_605_; 
v_hash_605_ = lean_ctor_get_uint64(v_a_586_, sizeof(void*)*2);
v___y_590_ = v_hash_605_;
goto v___jp_589_;
}
v___jp_589_:
{
uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v_fold_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_591_ = 32ULL;
v___x_592_ = lean_uint64_shift_right(v___y_590_, v___x_591_);
v_fold_593_ = lean_uint64_xor(v___y_590_, v___x_592_);
v___x_594_ = 16ULL;
v___x_595_ = lean_uint64_shift_right(v_fold_593_, v___x_594_);
v___x_596_ = lean_uint64_xor(v_fold_593_, v___x_595_);
v___x_597_ = lean_uint64_to_usize(v___x_596_);
v___x_598_ = lean_usize_of_nat(v___x_588_);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_sub(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_land(v___x_597_, v___x_600_);
v___x_602_ = lean_array_uget_borrowed(v_buckets_587_, v___x_601_);
v___x_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_586_, v___x_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg___boxed(lean_object* v_m_606_, lean_object* v_a_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg(v_m_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_m_606_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
return v_x_610_;
}
else
{
lean_object* v_key_612_; lean_object* v_value_613_; lean_object* v_tail_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_640_; 
v_key_612_ = lean_ctor_get(v_x_611_, 0);
v_value_613_ = lean_ctor_get(v_x_611_, 1);
v_tail_614_ = lean_ctor_get(v_x_611_, 2);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_640_ == 0)
{
v___x_616_ = v_x_611_;
v_isShared_617_ = v_isSharedCheck_640_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_tail_614_);
lean_inc(v_value_613_);
lean_inc(v_key_612_);
lean_dec(v_x_611_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_640_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; uint64_t v___y_620_; 
v___x_618_ = lean_array_get_size(v_x_610_);
if (lean_obj_tag(v_key_612_) == 0)
{
uint64_t v___x_638_; 
v___x_638_ = 1723ULL;
v___y_620_ = v___x_638_;
goto v___jp_619_;
}
else
{
uint64_t v_hash_639_; 
v_hash_639_ = lean_ctor_get_uint64(v_key_612_, sizeof(void*)*2);
v___y_620_ = v_hash_639_;
goto v___jp_619_;
}
v___jp_619_:
{
uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v_fold_623_; uint64_t v___x_624_; uint64_t v___x_625_; uint64_t v___x_626_; size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_621_ = 32ULL;
v___x_622_ = lean_uint64_shift_right(v___y_620_, v___x_621_);
v_fold_623_ = lean_uint64_xor(v___y_620_, v___x_622_);
v___x_624_ = 16ULL;
v___x_625_ = lean_uint64_shift_right(v_fold_623_, v___x_624_);
v___x_626_ = lean_uint64_xor(v_fold_623_, v___x_625_);
v___x_627_ = lean_uint64_to_usize(v___x_626_);
v___x_628_ = lean_usize_of_nat(v___x_618_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_sub(v___x_628_, v___x_629_);
v___x_631_ = lean_usize_land(v___x_627_, v___x_630_);
v___x_632_ = lean_array_uget_borrowed(v_x_610_, v___x_631_);
lean_inc(v___x_632_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 2, v___x_632_);
v___x_634_ = v___x_616_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_key_612_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_value_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v___x_632_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = lean_array_uset(v_x_610_, v___x_631_, v___x_634_);
v_x_610_ = v___x_635_;
v_x_611_ = v_tail_614_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3___redArg(lean_object* v_i_641_, lean_object* v_source_642_, lean_object* v_target_643_){
_start:
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_array_get_size(v_source_642_);
v___x_645_ = lean_nat_dec_lt(v_i_641_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v_source_642_);
lean_dec(v_i_641_);
return v_target_643_;
}
else
{
lean_object* v_es_646_; lean_object* v___x_647_; lean_object* v_source_648_; lean_object* v_target_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_es_646_ = lean_array_fget(v_source_642_, v_i_641_);
v___x_647_ = lean_box(0);
v_source_648_ = lean_array_fset(v_source_642_, v_i_641_, v___x_647_);
v_target_649_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3_spec__5___redArg(v_target_643_, v_es_646_);
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_add(v_i_641_, v___x_650_);
lean_dec(v_i_641_);
v_i_641_ = v___x_651_;
v_source_642_ = v_source_648_;
v_target_643_ = v_target_649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2___redArg(lean_object* v_data_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_nbuckets_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_654_ = lean_array_get_size(v_data_653_);
v___x_655_ = lean_unsigned_to_nat(2u);
v_nbuckets_656_ = lean_nat_mul(v___x_654_, v___x_655_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_box(0);
v___x_659_ = lean_mk_array(v_nbuckets_656_, v___x_658_);
v___x_660_ = lean_array_propagate_mark(v_data_653_, v___x_659_);
v___x_661_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3___redArg(v___x_657_, v_data_653_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1___redArg(lean_object* v_m_662_, lean_object* v_a_663_, lean_object* v_b_664_){
_start:
{
lean_object* v_size_665_; lean_object* v_buckets_666_; lean_object* v___x_667_; uint64_t v___y_669_; 
v_size_665_ = lean_ctor_get(v_m_662_, 0);
v_buckets_666_ = lean_ctor_get(v_m_662_, 1);
v___x_667_ = lean_array_get_size(v_buckets_666_);
if (lean_obj_tag(v_a_663_) == 0)
{
uint64_t v___x_706_; 
v___x_706_ = 1723ULL;
v___y_669_ = v___x_706_;
goto v___jp_668_;
}
else
{
uint64_t v_hash_707_; 
v_hash_707_ = lean_ctor_get_uint64(v_a_663_, sizeof(void*)*2);
v___y_669_ = v_hash_707_;
goto v___jp_668_;
}
v___jp_668_:
{
uint64_t v___x_670_; uint64_t v___x_671_; uint64_t v_fold_672_; uint64_t v___x_673_; uint64_t v___x_674_; uint64_t v___x_675_; size_t v___x_676_; size_t v___x_677_; size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; lean_object* v_bkt_681_; uint8_t v___x_682_; 
v___x_670_ = 32ULL;
v___x_671_ = lean_uint64_shift_right(v___y_669_, v___x_670_);
v_fold_672_ = lean_uint64_xor(v___y_669_, v___x_671_);
v___x_673_ = 16ULL;
v___x_674_ = lean_uint64_shift_right(v_fold_672_, v___x_673_);
v___x_675_ = lean_uint64_xor(v_fold_672_, v___x_674_);
v___x_676_ = lean_uint64_to_usize(v___x_675_);
v___x_677_ = lean_usize_of_nat(v___x_667_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_sub(v___x_677_, v___x_678_);
v___x_680_ = lean_usize_land(v___x_676_, v___x_679_);
v_bkt_681_ = lean_array_uget_borrowed(v_buckets_666_, v___x_680_);
v___x_682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_663_, v_bkt_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_buckets_666_);
lean_inc(v_size_665_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_m_662_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_704_ = lean_ctor_get(v_m_662_, 1);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_m_662_, 0);
lean_dec(v_unused_705_);
v___x_684_ = v_m_662_;
v_isShared_685_ = v_isSharedCheck_703_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_m_662_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_703_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v_size_x27_687_; lean_object* v___x_688_; lean_object* v_buckets_x27_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v_size_x27_687_ = lean_nat_add(v_size_665_, v___x_686_);
lean_dec(v_size_665_);
lean_inc(v_bkt_681_);
v___x_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_688_, 0, v_a_663_);
lean_ctor_set(v___x_688_, 1, v_b_664_);
lean_ctor_set(v___x_688_, 2, v_bkt_681_);
v_buckets_x27_689_ = lean_array_uset(v_buckets_666_, v___x_680_, v___x_688_);
v___x_690_ = lean_unsigned_to_nat(4u);
v___x_691_ = lean_nat_mul(v_size_x27_687_, v___x_690_);
v___x_692_ = lean_unsigned_to_nat(3u);
v___x_693_ = lean_nat_div(v___x_691_, v___x_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_array_get_size(v_buckets_x27_689_);
v___x_695_ = lean_nat_dec_le(v___x_693_, v___x_694_);
lean_dec(v___x_693_);
if (v___x_695_ == 0)
{
lean_object* v_val_696_; lean_object* v___x_698_; 
v_val_696_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2___redArg(v_buckets_x27_689_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_val_696_);
lean_ctor_set(v___x_684_, 0, v_size_x27_687_);
v___x_698_ = v___x_684_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_size_x27_687_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_val_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_701_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_buckets_x27_689_);
lean_ctor_set(v___x_684_, 0, v_size_x27_687_);
v___x_701_ = v___x_684_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_size_x27_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_buckets_x27_689_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_dec(v_b_664_);
lean_dec(v_a_663_);
return v_m_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0(lean_object* v_cur_710_, lean_object* v_cs_x3f_711_){
_start:
{
lean_object* v___y_713_; 
if (lean_obj_tag(v_cs_x3f_711_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0___closed__0));
v___y_713_ = v___x_716_;
goto v___jp_712_;
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v_cs_x3f_711_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_cs_x3f_711_, 1);
v___y_713_ = v_val_717_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_array_push(v___y_713_, v_cur_710_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4(lean_object* v_cur_718_, lean_object* v_a_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_val_723_; lean_object* v___x_724_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0(v_cur_718_, v___x_721_);
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_723_);
lean_dec(v___x_722_);
v___x_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_724_, 0, v_a_719_);
lean_ctor_set(v___x_724_, 1, v_val_723_);
lean_ctor_set(v___x_724_, 2, v_x_720_);
return v___x_724_;
}
else
{
lean_object* v_key_725_; lean_object* v_value_726_; lean_object* v_tail_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_742_; 
v_key_725_ = lean_ctor_get(v_x_720_, 0);
v_value_726_ = lean_ctor_get(v_x_720_, 1);
v_tail_727_ = lean_ctor_get(v_x_720_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_742_ == 0)
{
v___x_729_ = v_x_720_;
v_isShared_730_ = v_isSharedCheck_742_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_tail_727_);
lean_inc(v_value_726_);
lean_inc(v_key_725_);
lean_dec(v_x_720_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_742_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_731_; 
v___x_731_ = lean_name_eq(v_key_725_, v_a_719_);
if (v___x_731_ == 0)
{
lean_object* v_tail_732_; lean_object* v___x_734_; 
v_tail_732_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4(v_cur_718_, v_a_719_, v_tail_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 2, v_tail_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_key_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_value_726_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_tail_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_val_738_; lean_object* v___x_740_; 
lean_dec(v_key_725_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_value_726_);
v___x_737_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0(v_cur_718_, v___x_736_);
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec(v___x_737_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_val_738_);
lean_ctor_set(v___x_729_, 0, v_a_719_);
v___x_740_ = v___x_729_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_719_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_val_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_tail_727_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2(lean_object* v_cur_743_, lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___y_747_; lean_object* v___y_748_; size_t v___y_749_; lean_object* v___y_750_; lean_object* v_size_753_; lean_object* v_buckets_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_801_; 
v_size_753_ = lean_ctor_get(v_m_744_, 0);
v_buckets_754_ = lean_ctor_get(v_m_744_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_m_744_);
if (v_isSharedCheck_801_ == 0)
{
v___x_756_ = v_m_744_;
v_isShared_757_ = v_isSharedCheck_801_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_buckets_754_);
lean_inc(v_size_753_);
lean_dec(v_m_744_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_801_;
goto v_resetjp_755_;
}
v___jp_746_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_array_uset(v___y_747_, v___y_749_, v___y_748_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___y_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
return v___x_752_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; uint64_t v___y_760_; 
v___x_758_ = lean_array_get_size(v_buckets_754_);
if (lean_obj_tag(v_a_745_) == 0)
{
uint64_t v___x_799_; 
v___x_799_ = 1723ULL;
v___y_760_ = v___x_799_;
goto v___jp_759_;
}
else
{
uint64_t v_hash_800_; 
v_hash_800_ = lean_ctor_get_uint64(v_a_745_, sizeof(void*)*2);
v___y_760_ = v_hash_800_;
goto v___jp_759_;
}
v___jp_759_:
{
uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v_fold_763_; uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v___x_766_; size_t v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v_bkt_772_; uint8_t v___x_773_; 
v___x_761_ = 32ULL;
v___x_762_ = lean_uint64_shift_right(v___y_760_, v___x_761_);
v_fold_763_ = lean_uint64_xor(v___y_760_, v___x_762_);
v___x_764_ = 16ULL;
v___x_765_ = lean_uint64_shift_right(v_fold_763_, v___x_764_);
v___x_766_ = lean_uint64_xor(v_fold_763_, v___x_765_);
v___x_767_ = lean_uint64_to_usize(v___x_766_);
v___x_768_ = lean_usize_of_nat(v___x_758_);
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_sub(v___x_768_, v___x_769_);
v___x_771_ = lean_usize_land(v___x_767_, v___x_770_);
v_bkt_772_ = lean_array_uget_borrowed(v_buckets_754_, v___x_771_);
v___x_773_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_745_, v_bkt_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_size_x27_777_; lean_object* v___x_778_; lean_object* v_buckets_x27_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_774_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0___closed__0));
v___x_775_ = lean_array_push(v___x_774_, v_cur_743_);
v___x_776_ = lean_unsigned_to_nat(1u);
v_size_x27_777_ = lean_nat_add(v_size_753_, v___x_776_);
lean_dec(v_size_753_);
lean_inc(v_bkt_772_);
v___x_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_778_, 0, v_a_745_);
lean_ctor_set(v___x_778_, 1, v___x_775_);
lean_ctor_set(v___x_778_, 2, v_bkt_772_);
v_buckets_x27_779_ = lean_array_uset(v_buckets_754_, v___x_771_, v___x_778_);
v___x_780_ = lean_unsigned_to_nat(4u);
v___x_781_ = lean_nat_mul(v_size_x27_777_, v___x_780_);
v___x_782_ = lean_unsigned_to_nat(3u);
v___x_783_ = lean_nat_div(v___x_781_, v___x_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_array_get_size(v_buckets_x27_779_);
v___x_785_ = lean_nat_dec_le(v___x_783_, v___x_784_);
lean_dec(v___x_783_);
if (v___x_785_ == 0)
{
lean_object* v_val_786_; lean_object* v___x_788_; 
v_val_786_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2___redArg(v_buckets_x27_779_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_val_786_);
lean_ctor_set(v___x_756_, 0, v_size_x27_777_);
v___x_788_ = v___x_756_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_size_x27_777_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_val_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
lean_object* v___x_791_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_buckets_x27_779_);
lean_ctor_set(v___x_756_, 0, v_size_x27_777_);
v___x_791_ = v___x_756_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_size_x27_777_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_buckets_x27_779_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v___x_793_; lean_object* v_buckets_x27_794_; lean_object* v_bkt_x27_795_; uint8_t v___x_796_; 
lean_inc(v_bkt_772_);
lean_del_object(v___x_756_);
v___x_793_ = lean_box(0);
v_buckets_x27_794_ = lean_array_uset(v_buckets_754_, v___x_771_, v___x_793_);
lean_inc(v_a_745_);
v_bkt_x27_795_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4(v_cur_743_, v_a_745_, v_bkt_772_);
v___x_796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_745_, v_bkt_x27_795_);
lean_dec(v_a_745_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_sub(v_size_753_, v___x_797_);
lean_dec(v_size_753_);
v___y_747_ = v_buckets_x27_794_;
v___y_748_ = v_bkt_x27_795_;
v___y_749_ = v___x_771_;
v___y_750_ = v___x_798_;
goto v___jp_746_;
}
else
{
v___y_747_ = v_buckets_x27_794_;
v___y_748_ = v_bkt_x27_795_;
v___y_749_ = v___x_771_;
v___y_750_ = v_size_753_;
goto v___jp_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName___redArg(lean_object* v_b_802_, lean_object* v_cur_803_){
_start:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_name_eq(v_cur_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v_values_806_; lean_object* v_seen_807_; lean_object* v_children_808_; uint8_t v___x_809_; 
v_values_806_ = lean_ctor_get(v_b_802_, 0);
v_seen_807_ = lean_ctor_get(v_b_802_, 1);
v_children_808_ = lean_ctor_get(v_b_802_, 2);
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg(v_seen_807_, v_cur_803_);
if (v___x_809_ == 0)
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_823_; 
lean_inc_ref(v_children_808_);
lean_inc_ref(v_seen_807_);
lean_inc_ref(v_values_806_);
v_isSharedCheck_823_ = !lean_is_exclusive(v_b_802_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_824_ = lean_ctor_get(v_b_802_, 2);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_b_802_, 1);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_b_802_, 0);
lean_dec(v_unused_826_);
v___x_811_ = v_b_802_;
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_b_802_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___y_816_; 
v___x_813_ = lean_box(0);
lean_inc(v_cur_803_);
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1___redArg(v_seen_807_, v_cur_803_, v___x_813_);
if (lean_obj_tag(v_cur_803_) == 0)
{
v___y_816_ = v_cur_803_;
goto v___jp_815_;
}
else
{
lean_object* v_pre_822_; 
v_pre_822_ = lean_ctor_get(v_cur_803_, 0);
lean_inc(v_pre_822_);
v___y_816_ = v_pre_822_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_inc(v___y_816_);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2(v_cur_803_, v_children_808_, v___y_816_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 2, v___x_817_);
lean_ctor_set(v___x_811_, 1, v___x_814_);
v___x_819_ = v___x_811_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_values_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___x_817_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_b_802_ = v___x_819_;
v_cur_803_ = v___y_816_;
goto _start;
}
}
}
}
else
{
lean_dec(v_cur_803_);
return v_b_802_;
}
}
else
{
lean_dec(v_cur_803_);
return v_b_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName(lean_object* v_00_u03b1_827_, lean_object* v_b_828_, lean_object* v_cur_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName___redArg(v_b_828_, v_cur_829_);
return v___x_830_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0(lean_object* v_00_u03b2_831_, lean_object* v_m_832_, lean_object* v_a_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___redArg(v_m_832_, v_a_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0___boxed(lean_object* v_00_u03b2_835_, lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0(v_00_u03b2_835_, v_m_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_m_836_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1(lean_object* v_00_u03b2_840_, lean_object* v_m_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1___redArg(v_m_841_, v_a_842_, v_b_843_);
return v___x_844_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0(lean_object* v_00_u03b2_845_, lean_object* v_a_846_, lean_object* v_x_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0(v_00_u03b2_849_, v_a_850_, v_x_851_);
lean_dec(v_x_851_);
lean_dec(v_a_850_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2(lean_object* v_00_u03b2_854_, lean_object* v_data_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2___redArg(v_data_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_857_, lean_object* v_i_858_, lean_object* v_source_859_, lean_object* v_target_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3___redArg(v_i_858_, v_source_859_, v_target_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2_spec__3_spec__5___redArg(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg(lean_object* v_a_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_867_) == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_box(0);
return v___x_868_;
}
else
{
lean_object* v_key_869_; lean_object* v_value_870_; lean_object* v_tail_871_; uint8_t v___x_872_; 
v_key_869_ = lean_ctor_get(v_x_867_, 0);
v_value_870_ = lean_ctor_get(v_x_867_, 1);
v_tail_871_ = lean_ctor_get(v_x_867_, 2);
v___x_872_ = lean_name_eq(v_key_869_, v_a_866_);
if (v___x_872_ == 0)
{
v_x_867_ = v_tail_871_;
goto _start;
}
else
{
lean_object* v___x_874_; 
lean_inc(v_value_870_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v_value_870_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg___boxed(lean_object* v_a_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg(v_a_875_, v_x_876_);
lean_dec(v_x_876_);
lean_dec(v_a_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_buckets_880_; lean_object* v___x_881_; uint64_t v___y_883_; 
v_buckets_880_ = lean_ctor_get(v_m_878_, 1);
v___x_881_ = lean_array_get_size(v_buckets_880_);
if (lean_obj_tag(v_a_879_) == 0)
{
uint64_t v___x_897_; 
v___x_897_ = 1723ULL;
v___y_883_ = v___x_897_;
goto v___jp_882_;
}
else
{
uint64_t v_hash_898_; 
v_hash_898_ = lean_ctor_get_uint64(v_a_879_, sizeof(void*)*2);
v___y_883_ = v_hash_898_;
goto v___jp_882_;
}
v___jp_882_:
{
uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v_fold_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_884_ = 32ULL;
v___x_885_ = lean_uint64_shift_right(v___y_883_, v___x_884_);
v_fold_886_ = lean_uint64_xor(v___y_883_, v___x_885_);
v___x_887_ = 16ULL;
v___x_888_ = lean_uint64_shift_right(v_fold_886_, v___x_887_);
v___x_889_ = lean_uint64_xor(v_fold_886_, v___x_888_);
v___x_890_ = lean_uint64_to_usize(v___x_889_);
v___x_891_ = lean_usize_of_nat(v___x_881_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_sub(v___x_891_, v___x_892_);
v___x_894_ = lean_usize_land(v___x_890_, v___x_893_);
v___x_895_ = lean_array_uget_borrowed(v_buckets_880_, v___x_894_);
v___x_896_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg(v_a_879_, v___x_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg___boxed(lean_object* v_m_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(v_m_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_m_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg(lean_object* v_hi_902_, lean_object* v_pivot_903_, lean_object* v_as_904_, lean_object* v_i_905_, lean_object* v_k_906_){
_start:
{
uint64_t v___y_908_; uint64_t v___y_909_; uint64_t v___y_920_; lean_object* v___y_921_; uint64_t v___y_925_; lean_object* v___y_928_; uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_lt(v_k_906_, v_hi_902_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_k_906_);
v___x_932_ = lean_array_fswap(v_as_904_, v_i_905_, v_hi_902_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_i_905_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v_key_935_; 
v___x_934_ = lean_array_fget_borrowed(v_as_904_, v_k_906_);
v_key_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_key_935_);
v___y_928_ = v_key_935_;
goto v___jp_927_;
}
v___jp_907_:
{
uint8_t v___x_910_; 
v___x_910_ = lean_uint64_dec_lt(v___y_908_, v___y_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_k_906_, v___x_911_);
lean_dec(v_k_906_);
v_k_906_ = v___x_912_;
goto _start;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_914_ = lean_array_fswap(v_as_904_, v_i_905_, v_k_906_);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_i_905_, v___x_915_);
lean_dec(v_i_905_);
v___x_917_ = lean_nat_add(v_k_906_, v___x_915_);
lean_dec(v_k_906_);
v_as_904_ = v___x_914_;
v_i_905_ = v___x_916_;
v_k_906_ = v___x_917_;
goto _start;
}
}
v___jp_919_:
{
if (lean_obj_tag(v___y_921_) == 0)
{
uint64_t v___x_922_; 
v___x_922_ = 1723ULL;
v___y_908_ = v___y_920_;
v___y_909_ = v___x_922_;
goto v___jp_907_;
}
else
{
uint64_t v_hash_923_; 
v_hash_923_ = lean_ctor_get_uint64(v___y_921_, sizeof(void*)*2);
v___y_908_ = v___y_920_;
v___y_909_ = v_hash_923_;
goto v___jp_907_;
}
}
v___jp_924_:
{
lean_object* v_key_926_; 
v_key_926_ = lean_ctor_get(v_pivot_903_, 0);
v___y_920_ = v___y_925_;
v___y_921_ = v_key_926_;
goto v___jp_919_;
}
v___jp_927_:
{
if (lean_obj_tag(v___y_928_) == 0)
{
uint64_t v___x_929_; 
v___x_929_ = 1723ULL;
v___y_925_ = v___x_929_;
goto v___jp_924_;
}
else
{
uint64_t v_hash_930_; 
v_hash_930_ = lean_ctor_get_uint64(v___y_928_, sizeof(void*)*2);
lean_dec(v___y_928_);
v___y_925_ = v_hash_930_;
goto v___jp_924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg___boxed(lean_object* v_hi_936_, lean_object* v_pivot_937_, lean_object* v_as_938_, lean_object* v_i_939_, lean_object* v_k_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg(v_hi_936_, v_pivot_937_, v_as_938_, v_i_939_, v_k_940_);
lean_dec_ref(v_pivot_937_);
lean_dec(v_hi_936_);
return v_res_941_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0(lean_object* v_c_u2081_942_, lean_object* v_c_u2082_943_){
_start:
{
uint64_t v___y_945_; lean_object* v___y_946_; uint64_t v___y_952_; lean_object* v___y_955_; lean_object* v_key_958_; 
v_key_958_ = lean_ctor_get(v_c_u2081_942_, 0);
v___y_955_ = v_key_958_;
goto v___jp_954_;
v___jp_944_:
{
if (lean_obj_tag(v___y_946_) == 0)
{
uint64_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = 1723ULL;
v___x_948_ = lean_uint64_dec_lt(v___y_945_, v___x_947_);
return v___x_948_;
}
else
{
uint64_t v_hash_949_; uint8_t v___x_950_; 
v_hash_949_ = lean_ctor_get_uint64(v___y_946_, sizeof(void*)*2);
v___x_950_ = lean_uint64_dec_lt(v___y_945_, v_hash_949_);
return v___x_950_;
}
}
v___jp_951_:
{
lean_object* v_key_953_; 
v_key_953_ = lean_ctor_get(v_c_u2082_943_, 0);
v___y_945_ = v___y_952_;
v___y_946_ = v_key_953_;
goto v___jp_944_;
}
v___jp_954_:
{
if (lean_obj_tag(v___y_955_) == 0)
{
uint64_t v___x_956_; 
v___x_956_ = 1723ULL;
v___y_952_ = v___x_956_;
goto v___jp_951_;
}
else
{
uint64_t v_hash_957_; 
v_hash_957_ = lean_ctor_get_uint64(v___y_955_, sizeof(void*)*2);
v___y_952_ = v_hash_957_;
goto v___jp_951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0___boxed(lean_object* v_c_u2081_959_, lean_object* v_c_u2082_960_){
_start:
{
uint8_t v_res_961_; lean_object* v_r_962_; 
v_res_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0(v_c_u2081_959_, v_c_u2082_960_);
lean_dec_ref(v_c_u2082_960_);
lean_dec_ref(v_c_u2081_959_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg(lean_object* v_n_963_, lean_object* v_as_964_, lean_object* v_lo_965_, lean_object* v_hi_966_){
_start:
{
lean_object* v___y_968_; uint8_t v___x_978_; 
v___x_978_ = lean_nat_dec_lt(v_lo_965_, v_hi_966_);
if (v___x_978_ == 0)
{
lean_dec(v_lo_965_);
return v_as_964_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_mid_981_; lean_object* v___y_983_; lean_object* v___y_989_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_979_ = lean_nat_add(v_lo_965_, v_hi_966_);
v___x_980_ = lean_unsigned_to_nat(1u);
v_mid_981_ = lean_nat_shiftr(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
v___x_994_ = lean_array_fget_borrowed(v_as_964_, v_mid_981_);
v___x_995_ = lean_array_fget_borrowed(v_as_964_, v_lo_965_);
v___x_996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
v___y_989_ = v_as_964_;
goto v___jp_988_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = lean_array_fswap(v_as_964_, v_lo_965_, v_mid_981_);
v___y_989_ = v___x_997_;
goto v___jp_988_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = lean_array_fget_borrowed(v___y_983_, v_mid_981_);
v___x_985_ = lean_array_fget_borrowed(v___y_983_, v_hi_966_);
v___x_986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0(v___x_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_dec(v_mid_981_);
v___y_968_ = v___y_983_;
goto v___jp_967_;
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_array_fswap(v___y_983_, v_mid_981_, v_hi_966_);
lean_dec(v_mid_981_);
v___y_968_ = v___x_987_;
goto v___jp_967_;
}
}
v___jp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_array_fget_borrowed(v___y_989_, v_hi_966_);
v___x_991_ = lean_array_fget_borrowed(v___y_989_, v_lo_965_);
v___x_992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___lam__0(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
v___y_983_ = v___y_989_;
goto v___jp_982_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = lean_array_fswap(v___y_989_, v_lo_965_, v_hi_966_);
v___y_983_ = v___x_993_;
goto v___jp_982_;
}
}
}
v___jp_967_:
{
lean_object* v_pivot_969_; lean_object* v___x_970_; lean_object* v_fst_971_; lean_object* v_snd_972_; uint8_t v___x_973_; 
v_pivot_969_ = lean_array_fget(v___y_968_, v_hi_966_);
lean_inc_n(v_lo_965_, 2);
v___x_970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg(v_hi_966_, v_pivot_969_, v___y_968_, v_lo_965_, v_lo_965_);
lean_dec(v_pivot_969_);
v_fst_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_fst_971_);
v_snd_972_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_snd_972_);
lean_dec_ref(v___x_970_);
v___x_973_ = lean_nat_dec_le(v_hi_966_, v_fst_971_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg(v_n_963_, v_snd_972_, v_lo_965_, v_fst_971_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_add(v_fst_971_, v___x_975_);
lean_dec(v_fst_971_);
v_as_964_ = v___x_974_;
v_lo_965_ = v___x_976_;
goto _start;
}
else
{
lean_dec(v_fst_971_);
lean_dec(v_lo_965_);
return v_snd_972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg___boxed(lean_object* v_n_998_, lean_object* v_as_999_, lean_object* v_lo_1000_, lean_object* v_hi_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg(v_n_998_, v_as_999_, v_lo_1000_, v_hi_1001_);
lean_dec(v_hi_1001_);
lean_dec(v_n_998_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(lean_object* v_b_1003_, lean_object* v_key_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v_zero_1006_; uint8_t v_isZero_1007_; 
v_zero_1006_ = lean_unsigned_to_nat(0u);
v_isZero_1007_ = lean_nat_dec_eq(v_x_1005_, v_zero_1006_);
if (v_isZero_1007_ == 1)
{
lean_object* v_values_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_values_1008_ = lean_ctor_get(v_b_1003_, 0);
v___x_1009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(v_values_1008_, v_key_1004_);
v___x_1010_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
v___x_1011_ = l_Lean_ConstTrie_mk___redArg(v_key_1004_, v___x_1009_, v___x_1010_);
lean_dec(v___x_1009_);
return v___x_1011_;
}
else
{
lean_object* v_values_1012_; lean_object* v_children_1013_; lean_object* v___y_1015_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v_one_1030_; lean_object* v_n_1031_; lean_object* v___y_1033_; lean_object* v___x_1041_; 
v_values_1012_ = lean_ctor_get(v_b_1003_, 0);
v_children_1013_ = lean_ctor_get(v_b_1003_, 2);
v_one_1030_ = lean_unsigned_to_nat(1u);
v_n_1031_ = lean_nat_sub(v_x_1005_, v_one_1030_);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(v_children_1013_, v_key_1004_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__2_spec__4___lam__0___closed__0));
v___y_1033_ = v___x_1042_;
goto v___jp_1032_;
}
else
{
lean_object* v_val_1043_; 
v_val_1043_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_val_1043_);
lean_dec_ref_known(v___x_1041_, 1);
v___y_1033_ = v_val_1043_;
goto v___jp_1032_;
}
v___jp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(v_values_1012_, v_key_1004_);
v___x_1017_ = l_Lean_ConstTrie_mk___redArg(v_key_1004_, v___x_1016_, v___y_1015_);
lean_dec(v___x_1016_);
return v___x_1017_;
}
v___jp_1018_:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg(v___y_1021_, v___y_1020_, v___y_1019_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
v___y_1015_ = v___x_1023_;
goto v___jp_1014_;
}
v___jp_1024_:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_nat_dec_le(v___y_1028_, v___y_1025_);
if (v___x_1029_ == 0)
{
lean_dec(v___y_1025_);
lean_inc(v___y_1028_);
v___y_1019_ = v___y_1028_;
v___y_1020_ = v___y_1026_;
v___y_1021_ = v___y_1027_;
v___y_1022_ = v___y_1028_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___y_1028_;
v___y_1020_ = v___y_1026_;
v___y_1021_ = v___y_1027_;
v___y_1022_ = v___y_1025_;
goto v___jp_1018_;
}
}
v___jp_1032_:
{
size_t v_sz_1034_; size_t v___x_1035_; lean_object* v_children_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_sz_1034_ = lean_array_size(v___y_1033_);
v___x_1035_ = ((size_t)0ULL);
v_children_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg(v_b_1003_, v_n_1031_, v_sz_1034_, v___x_1035_, v___y_1033_);
lean_dec(v_n_1031_);
v___x_1037_ = lean_array_get_size(v_children_1036_);
v___x_1038_ = lean_nat_dec_eq(v___x_1037_, v_zero_1006_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_nat_sub(v___x_1037_, v_one_1030_);
v___x_1040_ = lean_nat_dec_le(v_zero_1006_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_inc(v___x_1039_);
v___y_1025_ = v___x_1039_;
v___y_1026_ = v_children_1036_;
v___y_1027_ = v___x_1037_;
v___y_1028_ = v___x_1039_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___x_1039_;
v___y_1026_ = v_children_1036_;
v___y_1027_ = v___x_1037_;
v___y_1028_ = v_zero_1006_;
goto v___jp_1024_;
}
}
else
{
v___y_1015_ = v_children_1036_;
goto v___jp_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg(lean_object* v_b_1044_, lean_object* v_n_1045_, size_t v_sz_1046_, size_t v_i_1047_, lean_object* v_bs_1048_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_usize_dec_lt(v_i_1047_, v_sz_1046_);
if (v___x_1049_ == 0)
{
return v_bs_1048_;
}
else
{
lean_object* v_v_1050_; lean_object* v___x_1051_; lean_object* v_bs_x27_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v_v_1050_ = lean_array_uget(v_bs_1048_, v_i_1047_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v_bs_x27_1052_ = lean_array_uset(v_bs_1048_, v_i_1047_, v___x_1051_);
v___x_1053_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(v_b_1044_, v_v_1050_, v_n_1045_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1047_, v___x_1054_);
v___x_1056_ = lean_array_uset(v_bs_x27_1052_, v_i_1047_, v___x_1053_);
v_i_1047_ = v___x_1055_;
v_bs_1048_ = v___x_1056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg___boxed(lean_object* v_b_1058_, lean_object* v_n_1059_, lean_object* v_sz_1060_, lean_object* v_i_1061_, lean_object* v_bs_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1060_);
lean_dec(v_sz_1060_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1061_);
lean_dec(v_i_1061_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg(v_b_1058_, v_n_1059_, v_sz_boxed_1063_, v_i_boxed_1064_, v_bs_1062_);
lean_dec(v_n_1059_);
lean_dec_ref(v_b_1058_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg___boxed(lean_object* v_b_1066_, lean_object* v_key_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(v_b_1066_, v_key_1067_, v_x_1068_);
lean_dec(v_x_1068_);
lean_dec_ref(v_b_1066_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie(lean_object* v_00_u03b1_1070_, lean_object* v_b_1071_, lean_object* v_key_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(v_b_1071_, v_key_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_b_1076_, lean_object* v_key_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie(v_00_u03b1_1075_, v_b_1076_, v_key_1077_, v_x_1078_);
lean_dec(v_x_1078_);
lean_dec_ref(v_b_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0(lean_object* v_00_u03b2_1080_, lean_object* v_m_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___redArg(v_m_1081_, v_a_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_m_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0(v_00_u03b2_1084_, v_m_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_m_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1(lean_object* v_00_u03b1_1088_, lean_object* v_b_1089_, lean_object* v_n_1090_, size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_bs_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___redArg(v_b_1089_, v_n_1090_, v_sz_1091_, v_i_1092_, v_bs_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_b_1096_, lean_object* v_n_1097_, lean_object* v_sz_1098_, lean_object* v_i_1099_, lean_object* v_bs_1100_){
_start:
{
size_t v_sz_boxed_1101_; size_t v_i_boxed_1102_; lean_object* v_res_1103_; 
v_sz_boxed_1101_ = lean_unbox_usize(v_sz_1098_);
lean_dec(v_sz_1098_);
v_i_boxed_1102_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__1(v_00_u03b1_1095_, v_b_1096_, v_n_1097_, v_sz_boxed_1101_, v_i_boxed_1102_, v_bs_1100_);
lean_dec(v_n_1097_);
lean_dec_ref(v_b_1096_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2(lean_object* v_00_u03b1_1104_, lean_object* v_n_1105_, lean_object* v_as_1106_, lean_object* v_lo_1107_, lean_object* v_hi_1108_, lean_object* v_w_1109_, lean_object* v_hlo_1110_, lean_object* v_hhi_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___redArg(v_n_1105_, v_as_1106_, v_lo_1107_, v_hi_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_n_1114_, lean_object* v_as_1115_, lean_object* v_lo_1116_, lean_object* v_hi_1117_, lean_object* v_w_1118_, lean_object* v_hlo_1119_, lean_object* v_hhi_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2(v_00_u03b1_1113_, v_n_1114_, v_as_1115_, v_lo_1116_, v_hi_1117_, v_w_1118_, v_hlo_1119_, v_hhi_1120_);
lean_dec(v_hi_1117_);
lean_dec(v_n_1114_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0(lean_object* v_00_u03b2_1122_, lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___redArg(v_a_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_a_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__0_spec__0(v_00_u03b2_1126_, v_a_1127_, v_x_1128_);
lean_dec(v_x_1128_);
lean_dec(v_a_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3(lean_object* v_00_u03b1_1130_, lean_object* v_n_1131_, lean_object* v_lo_1132_, lean_object* v_hi_1133_, lean_object* v_hhi_1134_, lean_object* v_pivot_1135_, lean_object* v_as_1136_, lean_object* v_i_1137_, lean_object* v_k_1138_, lean_object* v_ilo_1139_, lean_object* v_ik_1140_, lean_object* v_w_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___redArg(v_hi_1133_, v_pivot_1135_, v_as_1136_, v_i_1137_, v_k_1138_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_n_1144_, lean_object* v_lo_1145_, lean_object* v_hi_1146_, lean_object* v_hhi_1147_, lean_object* v_pivot_1148_, lean_object* v_as_1149_, lean_object* v_i_1150_, lean_object* v_k_1151_, lean_object* v_ilo_1152_, lean_object* v_ik_1153_, lean_object* v_w_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie_spec__2_spec__3(v_00_u03b1_1143_, v_n_1144_, v_lo_1145_, v_hi_1146_, v_hhi_1147_, v_pivot_1148_, v_as_1149_, v_i_1150_, v_k_1151_, v_ilo_1152_, v_ik_1153_, v_w_1154_);
lean_dec_ref(v_pivot_1148_);
lean_dec(v_hi_1146_);
lean_dec(v_lo_1145_);
lean_dec(v_n_1144_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound_spec__0(lean_object* v_as_1156_, size_t v_i_1157_, size_t v_stop_1158_, lean_object* v_b_1159_){
_start:
{
lean_object* v___y_1161_; uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_eq(v_i_1157_, v_stop_1158_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_array_uget_borrowed(v_as_1156_, v_i_1157_);
v___x_1167_ = l_Lean_Name_getNumParts(v___x_1166_);
v___x_1168_ = lean_nat_dec_le(v_b_1159_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_dec(v___x_1167_);
v___y_1161_ = v_b_1159_;
goto v___jp_1160_;
}
else
{
lean_dec(v_b_1159_);
v___y_1161_ = v___x_1167_;
goto v___jp_1160_;
}
}
else
{
return v_b_1159_;
}
v___jp_1160_:
{
size_t v___x_1162_; size_t v___x_1163_; 
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_add(v_i_1157_, v___x_1162_);
v_i_1157_ = v___x_1163_;
v_b_1159_ = v___y_1161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound_spec__0___boxed(lean_object* v_as_1169_, lean_object* v_i_1170_, lean_object* v_stop_1171_, lean_object* v_b_1172_){
_start:
{
size_t v_i_boxed_1173_; size_t v_stop_boxed_1174_; lean_object* v_res_1175_; 
v_i_boxed_1173_ = lean_unbox_usize(v_i_1170_);
lean_dec(v_i_1170_);
v_stop_boxed_1174_ = lean_unbox_usize(v_stop_1171_);
lean_dec(v_stop_1171_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound_spec__0(v_as_1169_, v_i_boxed_1173_, v_stop_boxed_1174_, v_b_1172_);
lean_dec_ref(v_as_1169_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound(lean_object* v_names_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_array_get_size(v_names_1176_);
v___x_1179_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
return v___x_1177_;
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1178_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound_spec__0(v_names_1176_, v___x_1180_, v___x_1181_, v___x_1177_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound___boxed(lean_object* v_names_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound(v_names_1183_);
lean_dec_ref(v_names_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0___redArg(lean_object* v_a_1185_, lean_object* v_b_1186_, lean_object* v_x_1187_){
_start:
{
if (lean_obj_tag(v_x_1187_) == 0)
{
lean_dec(v_b_1186_);
lean_dec(v_a_1185_);
return v_x_1187_;
}
else
{
lean_object* v_key_1188_; lean_object* v_value_1189_; lean_object* v_tail_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1202_; 
v_key_1188_ = lean_ctor_get(v_x_1187_, 0);
v_value_1189_ = lean_ctor_get(v_x_1187_, 1);
v_tail_1190_ = lean_ctor_get(v_x_1187_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1192_ = v_x_1187_;
v_isShared_1193_ = v_isSharedCheck_1202_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_tail_1190_);
lean_inc(v_value_1189_);
lean_inc(v_key_1188_);
lean_dec(v_x_1187_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1202_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_name_eq(v_key_1188_, v_a_1185_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0___redArg(v_a_1185_, v_b_1186_, v_tail_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 2, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_key_1188_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_value_1189_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
else
{
lean_object* v___x_1200_; 
lean_dec(v_value_1189_);
lean_dec(v_key_1188_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v_b_1186_);
lean_ctor_set(v___x_1192_, 0, v_a_1185_);
v___x_1200_ = v___x_1192_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1185_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_b_1186_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_tail_1190_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0___redArg(lean_object* v_m_1203_, lean_object* v_a_1204_, lean_object* v_b_1205_){
_start:
{
lean_object* v_size_1206_; lean_object* v_buckets_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1253_; 
v_size_1206_ = lean_ctor_get(v_m_1203_, 0);
v_buckets_1207_ = lean_ctor_get(v_m_1203_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_m_1203_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1209_ = v_m_1203_;
v_isShared_1210_ = v_isSharedCheck_1253_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_buckets_1207_);
lean_inc(v_size_1206_);
lean_dec(v_m_1203_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1253_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; uint64_t v___y_1213_; 
v___x_1211_ = lean_array_get_size(v_buckets_1207_);
if (lean_obj_tag(v_a_1204_) == 0)
{
uint64_t v___x_1251_; 
v___x_1251_ = 1723ULL;
v___y_1213_ = v___x_1251_;
goto v___jp_1212_;
}
else
{
uint64_t v_hash_1252_; 
v_hash_1252_ = lean_ctor_get_uint64(v_a_1204_, sizeof(void*)*2);
v___y_1213_ = v_hash_1252_;
goto v___jp_1212_;
}
v___jp_1212_:
{
uint64_t v___x_1214_; uint64_t v___x_1215_; uint64_t v_fold_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; uint64_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; lean_object* v_bkt_1225_; uint8_t v___x_1226_; 
v___x_1214_ = 32ULL;
v___x_1215_ = lean_uint64_shift_right(v___y_1213_, v___x_1214_);
v_fold_1216_ = lean_uint64_xor(v___y_1213_, v___x_1215_);
v___x_1217_ = 16ULL;
v___x_1218_ = lean_uint64_shift_right(v_fold_1216_, v___x_1217_);
v___x_1219_ = lean_uint64_xor(v_fold_1216_, v___x_1218_);
v___x_1220_ = lean_uint64_to_usize(v___x_1219_);
v___x_1221_ = lean_usize_of_nat(v___x_1211_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_sub(v___x_1221_, v___x_1222_);
v___x_1224_ = lean_usize_land(v___x_1220_, v___x_1223_);
v_bkt_1225_ = lean_array_uget_borrowed(v_buckets_1207_, v___x_1224_);
v___x_1226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__0_spec__0___redArg(v_a_1204_, v_bkt_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v_size_x27_1228_; lean_object* v___x_1229_; lean_object* v_buckets_x27_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1227_ = lean_unsigned_to_nat(1u);
v_size_x27_1228_ = lean_nat_add(v_size_1206_, v___x_1227_);
lean_dec(v_size_1206_);
lean_inc(v_bkt_1225_);
v___x_1229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1204_);
lean_ctor_set(v___x_1229_, 1, v_b_1205_);
lean_ctor_set(v___x_1229_, 2, v_bkt_1225_);
v_buckets_x27_1230_ = lean_array_uset(v_buckets_1207_, v___x_1224_, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(4u);
v___x_1232_ = lean_nat_mul(v_size_x27_1228_, v___x_1231_);
v___x_1233_ = lean_unsigned_to_nat(3u);
v___x_1234_ = lean_nat_div(v___x_1232_, v___x_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_array_get_size(v_buckets_x27_1230_);
v___x_1236_ = lean_nat_dec_le(v___x_1234_, v___x_1235_);
lean_dec(v___x_1234_);
if (v___x_1236_ == 0)
{
lean_object* v_val_1237_; lean_object* v___x_1239_; 
v_val_1237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName_spec__1_spec__2___redArg(v_buckets_x27_1230_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_val_1237_);
lean_ctor_set(v___x_1209_, 0, v_size_x27_1228_);
v___x_1239_ = v___x_1209_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_size_x27_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_val_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v___x_1242_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_buckets_x27_1230_);
lean_ctor_set(v___x_1209_, 0, v_size_x27_1228_);
v___x_1242_ = v___x_1209_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_size_x27_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_buckets_x27_1230_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v_buckets_x27_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_inc(v_bkt_1225_);
v___x_1244_ = lean_box(0);
v_buckets_x27_1245_ = lean_array_uset(v_buckets_1207_, v___x_1224_, v___x_1244_);
v___x_1246_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0___redArg(v_a_1204_, v_b_1205_, v_bkt_1225_);
v___x_1247_ = lean_array_uset(v_buckets_x27_1245_, v___x_1224_, v___x_1246_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1247_);
v___x_1249_ = v___x_1209_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_size_1206_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg(lean_object* v_names_1254_, lean_object* v_vals_1255_, lean_object* v_i_1256_, lean_object* v_b_1257_){
_start:
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = lean_array_get_size(v_names_1254_);
v___x_1259_ = lean_nat_dec_lt(v_i_1256_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v_i_1256_);
return v_b_1257_;
}
else
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = lean_array_get_size(v_vals_1255_);
v___x_1261_ = lean_nat_dec_lt(v_i_1256_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v_i_1256_);
return v_b_1257_;
}
else
{
lean_object* v_values_1262_; lean_object* v_seen_1263_; lean_object* v_children_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1278_; 
v_values_1262_ = lean_ctor_get(v_b_1257_, 0);
v_seen_1263_ = lean_ctor_get(v_b_1257_, 1);
v_children_1264_ = lean_ctor_get(v_b_1257_, 2);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_b_1257_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1266_ = v_b_1257_;
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_children_1264_);
lean_inc(v_seen_1263_);
lean_inc(v_values_1262_);
lean_dec(v_b_1257_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_b_1272_; 
v___x_1268_ = lean_array_fget_borrowed(v_names_1254_, v_i_1256_);
v___x_1269_ = lean_array_fget_borrowed(v_vals_1255_, v_i_1256_);
lean_inc(v___x_1269_);
lean_inc(v___x_1268_);
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0___redArg(v_values_1262_, v___x_1268_, v___x_1269_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1270_);
v_b_1272_ = v___x_1266_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_seen_1263_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_children_1264_);
v_b_1272_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_add(v_i_1256_, v___x_1273_);
lean_dec(v_i_1256_);
lean_inc(v___x_1268_);
v___x_1275_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName___redArg(v_b_1272_, v___x_1268_);
v_i_1256_ = v___x_1274_;
v_b_1257_ = v___x_1275_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg___boxed(lean_object* v_names_1279_, lean_object* v_vals_1280_, lean_object* v_i_1281_, lean_object* v_b_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg(v_names_1279_, v_vals_1280_, v_i_1281_, v_b_1282_);
lean_dec_ref(v_vals_1280_);
lean_dec_ref(v_names_1279_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go(lean_object* v_00_u03b1_1284_, lean_object* v_names_1285_, lean_object* v_vals_1286_, lean_object* v_i_1287_, lean_object* v_b_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg(v_names_1285_, v_vals_1286_, v_i_1287_, v_b_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___boxed(lean_object* v_00_u03b1_1290_, lean_object* v_names_1291_, lean_object* v_vals_1292_, lean_object* v_i_1293_, lean_object* v_b_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go(v_00_u03b1_1290_, v_names_1291_, v_vals_1292_, v_i_1293_, v_b_1294_);
lean_dec_ref(v_vals_1292_);
lean_dec_ref(v_names_1291_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0(lean_object* v_00_u03b2_1296_, lean_object* v_m_1297_, lean_object* v_a_1298_, lean_object* v_b_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0___redArg(v_m_1297_, v_a_1298_, v_b_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0(lean_object* v_00_u03b2_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0_spec__0___redArg(v_a_1302_, v_b_1303_, v_x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_ConstTrie_ofArrays___redArg___closed__0(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_unsigned_to_nat(16u);
v___x_1308_ = lean_mk_array(v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_ConstTrie_ofArrays___redArg___closed__1(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_obj_once(&l_Lean_ConstTrie_ofArrays___redArg___closed__0, &l_Lean_ConstTrie_ofArrays___redArg___closed__0_once, _init_l_Lean_ConstTrie_ofArrays___redArg___closed__0);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_ConstTrie_ofArrays___redArg___closed__2(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Lean_ConstTrie_ofArrays___redArg___closed__1, &l_Lean_ConstTrie_ofArrays___redArg___closed__1_once, _init_l_Lean_ConstTrie_ofArrays___redArg___closed__1);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays___redArg(lean_object* v_names_1314_, lean_object* v_vals_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_obj_once(&l_Lean_ConstTrie_ofArrays___redArg___closed__2, &l_Lean_ConstTrie_ofArrays___redArg___closed__2_once, _init_l_Lean_ConstTrie_ofArrays___redArg___closed__2);
v___x_1318_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go___redArg(v_names_1314_, v_vals_1315_, v___x_1316_, v___x_1317_);
v___x_1319_ = lean_box(0);
v___x_1320_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound(v_names_1314_);
v___x_1321_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(v___x_1318_, v___x_1319_, v___x_1320_);
lean_dec(v___x_1320_);
lean_dec_ref(v___x_1318_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays___redArg___boxed(lean_object* v_names_1322_, lean_object* v_vals_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_ConstTrie_ofArrays___redArg(v_names_1322_, v_vals_1323_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_names_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays(lean_object* v_00_u03b1_1325_, lean_object* v_names_1326_, lean_object* v_vals_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_ConstTrie_ofArrays___redArg(v_names_1326_, v_vals_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofArrays___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_names_1330_, lean_object* v_vals_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_ConstTrie_ofArrays(v_00_u03b1_1329_, v_names_1330_, v_vals_1331_);
lean_dec_ref(v_vals_1331_);
lean_dec_ref(v_names_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ConstTrie_ofNames_spec__0(lean_object* v_as_1333_, size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_b_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1337_ == 0)
{
return v_b_1336_;
}
else
{
lean_object* v_values_1338_; lean_object* v_seen_1339_; lean_object* v_children_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1354_; 
v_values_1338_ = lean_ctor_get(v_b_1336_, 0);
v_seen_1339_ = lean_ctor_get(v_b_1336_, 1);
v_children_1340_ = lean_ctor_get(v_b_1336_, 2);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_b_1336_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1342_ = v_b_1336_;
v_isShared_1343_ = v_isSharedCheck_1354_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_children_1340_);
lean_inc(v_seen_1339_);
lean_inc(v_values_1338_);
lean_dec(v_b_1336_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1354_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v_a_1344_ = lean_array_uget_borrowed(v_as_1333_, v_i_1335_);
v___x_1345_ = lean_box(0);
lean_inc(v_a_1344_);
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_ConstTrie_0__Lean_ConstTrie_ofArrays_go_spec__0___redArg(v_values_1338_, v_a_1344_, v___x_1345_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1346_);
v___x_1348_ = v___x_1342_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_seen_1339_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_children_1340_);
v___x_1348_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; 
lean_inc(v_a_1344_);
v___x_1349_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_addName___redArg(v___x_1348_, v_a_1344_);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1335_, v___x_1350_);
v_i_1335_ = v___x_1351_;
v_b_1336_ = v___x_1349_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ConstTrie_ofNames_spec__0___boxed(lean_object* v_as_1355_, lean_object* v_sz_1356_, lean_object* v_i_1357_, lean_object* v_b_1358_){
_start:
{
size_t v_sz_boxed_1359_; size_t v_i_boxed_1360_; lean_object* v_res_1361_; 
v_sz_boxed_1359_ = lean_unbox_usize(v_sz_1356_);
lean_dec(v_sz_1356_);
v_i_boxed_1360_ = lean_unbox_usize(v_i_1357_);
lean_dec(v_i_1357_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ConstTrie_ofNames_spec__0(v_as_1355_, v_sz_boxed_1359_, v_i_boxed_1360_, v_b_1358_);
lean_dec_ref(v_as_1355_);
return v_res_1361_;
}
}
static lean_object* _init_l_Lean_ConstTrie_ofNames___closed__0(void){
_start:
{
lean_object* v___x_1362_; lean_object* v_b_1363_; 
v___x_1362_ = lean_obj_once(&l_Lean_ConstTrie_ofArrays___redArg___closed__1, &l_Lean_ConstTrie_ofArrays___redArg___closed__1_once, _init_l_Lean_ConstTrie_ofArrays___redArg___closed__1);
v_b_1363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_b_1363_, 0, v___x_1362_);
lean_ctor_set(v_b_1363_, 1, v___x_1362_);
lean_ctor_set(v_b_1363_, 2, v___x_1362_);
return v_b_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofNames(lean_object* v_names_1364_){
_start:
{
lean_object* v_b_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_b_1365_ = lean_obj_once(&l_Lean_ConstTrie_ofNames___closed__0, &l_Lean_ConstTrie_ofNames___closed__0_once, _init_l_Lean_ConstTrie_ofNames___closed__0);
v_sz_1366_ = lean_array_size(v_names_1364_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ConstTrie_ofNames_spec__0(v_names_1364_, v_sz_1366_, v___x_1367_, v_b_1365_);
v___x_1369_ = lean_box(0);
v___x_1370_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_depthBound(v_names_1364_);
v___x_1371_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_Builder_toTrie___redArg(v___x_1368_, v___x_1369_, v___x_1370_);
lean_dec(v___x_1370_);
lean_dec_ref(v___x_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_ofNames___boxed(lean_object* v_names_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_ConstTrie_ofNames(v_names_1372_);
lean_dec_ref(v_names_1372_);
return v_res_1373_;
}
}
static lean_object* _init_l___private_Lean_ConstTrie_0__Lean_LookupCacheImpl(void){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_box(0);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_LookupCache_new___boxed(lean_object* v_a_00___x40___internal___hyg_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = lean_imported_consts_cache_new();
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl___redArg(lean_object* v_x_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_obj_tag_nat(v_x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl___redArg___boxed(lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_ImportedTree_ctorIdx___impl___redArg(v_x_1380_);
lean_dec_ref(v_x_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl(lean_object* v_00_u03b1_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_obj_tag_nat(v_x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorIdx___impl___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_ImportedTree_ctorIdx___impl(v_00_u03b1_1385_, v_x_1386_);
lean_dec_ref(v_x_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorElim___redArg(lean_object* v_t_1388_, lean_object* v_k_1389_){
_start:
{
if (lean_obj_tag(v_t_1388_) == 0)
{
lean_object* v_modIdx_1390_; lean_object* v_tree_1391_; lean_object* v___x_1392_; 
v_modIdx_1390_ = lean_ctor_get(v_t_1388_, 0);
lean_inc(v_modIdx_1390_);
v_tree_1391_ = lean_ctor_get(v_t_1388_, 1);
lean_inc_ref(v_tree_1391_);
lean_dec_ref_known(v_t_1388_, 2);
v___x_1392_ = lean_apply_2(v_k_1389_, v_modIdx_1390_, v_tree_1391_);
return v___x_1392_;
}
else
{
lean_object* v_key_1393_; lean_object* v_entry_x3f_1394_; lean_object* v_children_1395_; lean_object* v___x_1396_; 
v_key_1393_ = lean_ctor_get(v_t_1388_, 0);
lean_inc(v_key_1393_);
v_entry_x3f_1394_ = lean_ctor_get(v_t_1388_, 1);
lean_inc(v_entry_x3f_1394_);
v_children_1395_ = lean_ctor_get(v_t_1388_, 2);
lean_inc_ref(v_children_1395_);
lean_dec_ref(v_t_1388_);
v___x_1396_ = lean_apply_3(v_k_1389_, v_key_1393_, v_entry_x3f_1394_, v_children_1395_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorElim(lean_object* v_00_u03b1_1397_, lean_object* v_motive__1_1398_, lean_object* v_ctorIdx_1399_, lean_object* v_t_1400_, lean_object* v_h_1401_, lean_object* v_k_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1400_, v_k_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_ctorElim___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_motive__1_1405_, lean_object* v_ctorIdx_1406_, lean_object* v_t_1407_, lean_object* v_h_1408_, lean_object* v_k_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_ImportedTree_ctorElim(v_00_u03b1_1404_, v_motive__1_1405_, v_ctorIdx_1406_, v_t_1407_, v_h_1408_, v_k_1409_);
lean_dec(v_ctorIdx_1406_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_mod_elim___redArg(lean_object* v_t_1411_, lean_object* v_mod_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1411_, v_mod_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_mod_elim(lean_object* v_00_u03b1_1414_, lean_object* v_motive__1_1415_, lean_object* v_t_1416_, lean_object* v_h_1417_, lean_object* v_mod_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1416_, v_mod_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_merged_elim___redArg(lean_object* v_t_1420_, lean_object* v_merged_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1420_, v_merged_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_merged_elim(lean_object* v_00_u03b1_1423_, lean_object* v_motive__1_1424_, lean_object* v_t_1425_, lean_object* v_h_1426_, lean_object* v_merged_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1425_, v_merged_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_lazy_elim___redArg(lean_object* v_t_1429_, lean_object* v_lazy_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1429_, v_lazy_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedTree_lazy_elim(lean_object* v_00_u03b1_1432_, lean_object* v_motive__1_1433_, lean_object* v_t_1434_, lean_object* v_h_1435_, lean_object* v_lazy_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_ImportedTree_ctorElim___redArg(v_t_1434_, v_lazy_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedTree___redArg(){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l_Lean_instInhabitedImportedTree___redArg___closed__1));
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedTree___redArg___boxed(lean_object* v___dummy_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_instInhabitedImportedTree___redArg();
return v_res_1447_;
}
}
static lean_object* _init_l_Lean_instInhabitedImportedTree___closed__0(void){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_instInhabitedImportedTree___redArg();
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedTree(lean_object* v_00_u03b1_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_obj_once(&l_Lean_instInhabitedImportedTree___closed__0, &l_Lean_instInhabitedImportedTree___closed__0_once, _init_l_Lean_instInhabitedImportedTree___closed__0);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedConsts___redArg(){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = ((lean_object*)(l_Lean_instInhabitedImportedConsts___redArg___closed__1));
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedConsts___redArg___boxed(lean_object* v___dummy_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_instInhabitedImportedConsts___redArg();
return v_res_1461_;
}
}
static lean_object* _init_l_Lean_instInhabitedImportedConsts___closed__0(void){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_instInhabitedImportedConsts___redArg();
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedConsts(lean_object* v_00_u03b1_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_obj_once(&l_Lean_instInhabitedImportedConsts___closed__0, &l_Lean_instInhabitedImportedConsts___closed__0_once, _init_l_Lean_instInhabitedImportedConsts___closed__0);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg(lean_object* v_x_1465_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
lean_object* v_tree_1466_; lean_object* v_key_1467_; 
v_tree_1466_ = lean_ctor_get(v_x_1465_, 1);
v_key_1467_ = lean_ctor_get(v_tree_1466_, 0);
lean_inc(v_key_1467_);
return v_key_1467_;
}
else
{
lean_object* v_key_1468_; 
v_key_1468_ = lean_ctor_get(v_x_1465_, 0);
lean_inc(v_key_1468_);
return v_key_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg___boxed(lean_object* v_x_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg(v_x_1469_);
lean_dec_ref(v_x_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key(lean_object* v_00_u03b1_1471_, lean_object* v_x_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg(v_x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_key(v_00_u03b1_1474_, v_x_1475_);
lean_dec_ref(v_x_1475_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg(lean_object* v_cs_1477_, uint64_t v_h_1478_, lean_object* v_lo_1479_, lean_object* v_hi_1480_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_nat_dec_lt(v_lo_1479_, v_hi_1480_);
if (v___x_1481_ == 0)
{
lean_dec(v_hi_1480_);
return v_lo_1479_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_mid_1485_; uint64_t v___y_1487_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1482_ = lean_obj_once(&l_Lean_instInhabitedImportedTree___closed__0, &l_Lean_instInhabitedImportedTree___closed__0_once, _init_l_Lean_instInhabitedImportedTree___closed__0);
v___x_1483_ = lean_nat_add(v_lo_1479_, v_hi_1480_);
v___x_1484_ = lean_unsigned_to_nat(1u);
v_mid_1485_ = lean_nat_shiftr(v___x_1483_, v___x_1484_);
lean_dec(v___x_1483_);
v___x_1492_ = lean_array_get_borrowed(v___x_1482_, v_cs_1477_, v_mid_1485_);
v___x_1493_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg(v___x_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
uint64_t v___x_1494_; 
v___x_1494_ = 1723ULL;
v___y_1487_ = v___x_1494_;
goto v___jp_1486_;
}
else
{
uint64_t v_hash_1495_; 
v_hash_1495_ = lean_ctor_get_uint64(v___x_1493_, sizeof(void*)*2);
lean_dec(v___x_1493_);
v___y_1487_ = v_hash_1495_;
goto v___jp_1486_;
}
v___jp_1486_:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_uint64_dec_lt(v___y_1487_, v_h_1478_);
if (v___x_1488_ == 0)
{
lean_dec(v_hi_1480_);
v_hi_1480_ = v_mid_1485_;
goto _start;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v_lo_1479_);
v___x_1490_ = lean_nat_add(v_mid_1485_, v___x_1484_);
lean_dec(v_mid_1485_);
v_lo_1479_ = v___x_1490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg___boxed(lean_object* v_cs_1496_, lean_object* v_h_1497_, lean_object* v_lo_1498_, lean_object* v_hi_1499_){
_start:
{
uint64_t v_h_boxed_1500_; lean_object* v_res_1501_; 
v_h_boxed_1500_ = lean_unbox_uint64(v_h_1497_);
lean_dec_ref(v_h_1497_);
v_res_1501_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg(v_cs_1496_, v_h_boxed_1500_, v_lo_1498_, v_hi_1499_);
lean_dec_ref(v_cs_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg(lean_object* v_cs_1502_, lean_object* v_k_1503_, uint64_t v_h_1504_, lean_object* v_j_1505_){
_start:
{
uint8_t v___y_1511_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = lean_array_get_size(v_cs_1502_);
v___x_1514_ = lean_nat_dec_lt(v_j_1505_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_dec(v_j_1505_);
v___x_1515_ = lean_box(0);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_c_1518_; uint64_t v___y_1520_; 
v___x_1516_ = lean_obj_once(&l_Lean_instInhabitedImportedTree___closed__0, &l_Lean_instInhabitedImportedTree___closed__0_once, _init_l_Lean_instInhabitedImportedTree___closed__0);
v___x_1517_ = lean_array_get_borrowed(v___x_1516_, v_cs_1502_, v_j_1505_);
v_c_1518_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_key___redArg(v___x_1517_);
if (lean_obj_tag(v_c_1518_) == 0)
{
uint64_t v___x_1530_; 
v___x_1530_ = 1723ULL;
v___y_1520_ = v___x_1530_;
goto v___jp_1519_;
}
else
{
uint64_t v_hash_1531_; 
v_hash_1531_ = lean_ctor_get_uint64(v_c_1518_, sizeof(void*)*2);
v___y_1520_ = v_hash_1531_;
goto v___jp_1519_;
}
v___jp_1519_:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_uint64_dec_eq(v___y_1520_, v_h_1504_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec(v_c_1518_);
lean_dec(v_j_1505_);
v___x_1522_ = lean_box(0);
return v___x_1522_;
}
else
{
switch(lean_obj_tag(v_c_1518_))
{
case 0:
{
if (lean_obj_tag(v_k_1503_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_j_1505_);
return v___x_1523_;
}
else
{
goto v___jp_1506_;
}
}
case 1:
{
if (lean_obj_tag(v_k_1503_) == 1)
{
lean_object* v_str_1524_; lean_object* v_str_1525_; uint8_t v___x_1526_; 
v_str_1524_ = lean_ctor_get(v_c_1518_, 1);
lean_inc_ref(v_str_1524_);
lean_dec_ref_known(v_c_1518_, 2);
v_str_1525_ = lean_ctor_get(v_k_1503_, 1);
v___x_1526_ = lean_string_dec_eq(v_str_1524_, v_str_1525_);
lean_dec_ref(v_str_1524_);
v___y_1511_ = v___x_1526_;
goto v___jp_1510_;
}
else
{
lean_dec_ref_known(v_c_1518_, 2);
goto v___jp_1506_;
}
}
default: 
{
if (lean_obj_tag(v_k_1503_) == 2)
{
lean_object* v_i_1527_; lean_object* v_i_1528_; uint8_t v___x_1529_; 
v_i_1527_ = lean_ctor_get(v_c_1518_, 1);
lean_inc(v_i_1527_);
lean_dec_ref_known(v_c_1518_, 2);
v_i_1528_ = lean_ctor_get(v_k_1503_, 1);
v___x_1529_ = lean_nat_dec_eq(v_i_1527_, v_i_1528_);
lean_dec(v_i_1527_);
v___y_1511_ = v___x_1529_;
goto v___jp_1510_;
}
else
{
lean_dec_ref_known(v_c_1518_, 2);
goto v___jp_1506_;
}
}
}
}
}
}
v___jp_1506_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_nat_add(v_j_1505_, v___x_1507_);
lean_dec(v_j_1505_);
v_j_1505_ = v___x_1508_;
goto _start;
}
v___jp_1510_:
{
if (v___y_1511_ == 0)
{
goto v___jp_1506_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_j_1505_);
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg___boxed(lean_object* v_cs_1532_, lean_object* v_k_1533_, lean_object* v_h_1534_, lean_object* v_j_1535_){
_start:
{
uint64_t v_h_boxed_1536_; lean_object* v_res_1537_; 
v_h_boxed_1536_ = lean_unbox_uint64(v_h_1534_);
lean_dec_ref(v_h_1534_);
v_res_1537_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg(v_cs_1532_, v_k_1533_, v_h_boxed_1536_, v_j_1535_);
lean_dec(v_k_1533_);
lean_dec_ref(v_cs_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(lean_object* v_cs_1538_, lean_object* v_k_1539_){
_start:
{
uint64_t v___y_1541_; 
if (lean_obj_tag(v_k_1539_) == 0)
{
uint64_t v___x_1546_; 
v___x_1546_ = 1723ULL;
v___y_1541_ = v___x_1546_;
goto v___jp_1540_;
}
else
{
uint64_t v_hash_1547_; 
v_hash_1547_ = lean_ctor_get_uint64(v_k_1539_, sizeof(void*)*2);
v___y_1541_ = v_hash_1547_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_array_get_size(v_cs_1538_);
v___x_1544_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg(v_cs_1538_, v___y_1541_, v___x_1542_, v___x_1543_);
v___x_1545_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg(v_cs_1538_, v_k_1539_, v___y_1541_, v___x_1544_);
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg___boxed(lean_object* v_cs_1548_, lean_object* v_k_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(v_cs_1548_, v_k_1549_);
lean_dec(v_k_1549_);
lean_dec_ref(v_cs_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg(lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_obj_once(&l_Lean_instInhabitedImportedTree___closed__0, &l_Lean_instInhabitedImportedTree___closed__0_once, _init_l_Lean_instInhabitedImportedTree___closed__0);
switch(lean_obj_tag(v_x_1551_))
{
case 0:
{
lean_object* v_tree_1556_; lean_object* v___x_1557_; 
v_tree_1556_ = lean_ctor_get(v_x_1551_, 1);
lean_inc_ref(v_tree_1556_);
lean_dec_ref_known(v_x_1551_, 2);
v___x_1557_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(v_tree_1556_, v_x_1552_, v_x_1553_);
lean_dec_ref(v_tree_1556_);
return v___x_1557_;
}
case 1:
{
lean_object* v_entry_x3f_1558_; lean_object* v_children_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_entry_x3f_1558_ = lean_ctor_get(v_x_1551_, 1);
lean_inc(v_entry_x3f_1558_);
v_children_1559_ = lean_ctor_get(v_x_1551_, 2);
lean_inc_ref(v_children_1559_);
lean_dec_ref_known(v_x_1551_, 3);
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_nat_dec_eq(v_x_1553_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v_entry_x3f_1558_);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_sub(v_x_1553_, v___x_1562_);
lean_dec(v_x_1553_);
v___x_1564_ = lean_array_get_borrowed(v___x_1554_, v_x_1552_, v___x_1563_);
v___x_1565_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(v_children_1559_, v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; 
lean_dec(v___x_1563_);
lean_dec_ref(v_children_1559_);
v___x_1566_ = lean_box(0);
return v___x_1566_;
}
else
{
lean_object* v_val_1567_; lean_object* v___x_1568_; 
v_val_1567_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1568_ = lean_array_get(v___x_1555_, v_children_1559_, v_val_1567_);
lean_dec(v_val_1567_);
lean_dec_ref(v_children_1559_);
v_x_1551_ = v___x_1568_;
v_x_1553_ = v___x_1563_;
goto _start;
}
}
else
{
lean_dec_ref(v_children_1559_);
lean_dec(v_x_1553_);
if (lean_obj_tag(v_entry_x3f_1558_) == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_box(0);
return v___x_1570_;
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1579_; 
v_val_1571_ = lean_ctor_get(v_entry_x3f_1558_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_entry_x3f_1558_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1573_ = v_entry_x3f_1558_;
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_val_1571_);
lean_dec(v_entry_x3f_1558_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_fst_1575_; lean_object* v___x_1577_; 
v_fst_1575_ = lean_ctor_get(v_val_1571_, 0);
lean_inc(v_fst_1575_);
lean_dec(v_val_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_fst_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_fst_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
default: 
{
lean_object* v_entry_x3f_1580_; lean_object* v_children_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_entry_x3f_1580_ = lean_ctor_get(v_x_1551_, 1);
lean_inc(v_entry_x3f_1580_);
v_children_1581_ = lean_ctor_get(v_x_1551_, 2);
lean_inc_ref(v_children_1581_);
lean_dec_ref_known(v_x_1551_, 3);
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = lean_nat_dec_eq(v_x_1553_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v_cs_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v_entry_x3f_1580_);
v_cs_1584_ = lean_thunk_get_own(v_children_1581_);
lean_dec_ref(v_children_1581_);
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_nat_sub(v_x_1553_, v___x_1585_);
lean_dec(v_x_1553_);
v___x_1587_ = lean_array_get_borrowed(v___x_1554_, v_x_1552_, v___x_1586_);
v___x_1588_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(v_cs_1584_, v___x_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; 
lean_dec(v___x_1586_);
lean_dec(v_cs_1584_);
v___x_1589_ = lean_box(0);
return v___x_1589_;
}
else
{
lean_object* v_val_1590_; lean_object* v___x_1591_; 
v_val_1590_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1591_ = lean_array_get(v___x_1555_, v_cs_1584_, v_val_1590_);
lean_dec(v_val_1590_);
lean_dec(v_cs_1584_);
v_x_1551_ = v___x_1591_;
v_x_1553_ = v___x_1586_;
goto _start;
}
}
else
{
lean_dec_ref(v_children_1581_);
lean_dec(v_x_1553_);
if (lean_obj_tag(v_entry_x3f_1580_) == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_box(0);
return v___x_1593_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1602_; 
v_val_1594_ = lean_ctor_get(v_entry_x3f_1580_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_entry_x3f_1580_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1596_ = v_entry_x3f_1580_;
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v_entry_x3f_1580_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; lean_object* v___x_1600_; 
v_fst_1598_ = lean_ctor_get(v_val_1594_, 0);
lean_inc(v_fst_1598_);
lean_dec(v_val_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_fst_1598_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_fst_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg___boxed(lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg(v_x_1603_, v_x_1604_, v_x_1605_);
lean_dec_ref(v_x_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux(lean_object* v_00_u03b1_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg(v_x_1608_, v_x_1609_, v_x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux(v_00_u03b1_1612_, v_x_1613_, v_x_1614_, v_x_1615_);
lean_dec_ref(v_x_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0(lean_object* v_00_u03b1_1617_, lean_object* v_cs_1618_, lean_object* v_k_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(v_cs_1618_, v_k_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___boxed(lean_object* v_00_u03b1_1621_, lean_object* v_cs_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0(v_00_u03b1_1621_, v_cs_1622_, v_k_1623_);
lean_dec(v_k_1623_);
lean_dec_ref(v_cs_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0(lean_object* v_00_u03b1_1625_, lean_object* v_cs_1626_, uint64_t v_h_1627_, lean_object* v_lo_1628_, lean_object* v_hi_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___redArg(v_cs_1626_, v_h_1627_, v_lo_1628_, v_hi_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_cs_1632_, lean_object* v_h_1633_, lean_object* v_lo_1634_, lean_object* v_hi_1635_){
_start:
{
uint64_t v_h_boxed_1636_; lean_object* v_res_1637_; 
v_h_boxed_1636_ = lean_unbox_uint64(v_h_1633_);
lean_dec_ref(v_h_1633_);
v_res_1637_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_lowerBound___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__0(v_00_u03b1_1631_, v_cs_1632_, v_h_boxed_1636_, v_lo_1634_, v_hi_1635_);
lean_dec_ref(v_cs_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1(lean_object* v_00_u03b1_1638_, lean_object* v_cs_1639_, lean_object* v_k_1640_, uint64_t v_h_1641_, lean_object* v_j_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___redArg(v_cs_1639_, v_k_1640_, v_h_1641_, v_j_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_cs_1645_, lean_object* v_k_1646_, lean_object* v_h_1647_, lean_object* v_j_1648_){
_start:
{
uint64_t v_h_boxed_1649_; lean_object* v_res_1650_; 
v_h_boxed_1649_ = lean_unbox_uint64(v_h_1647_);
lean_dec_ref(v_h_1647_);
v_res_1650_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f_scanRun___at___00__private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0_spec__1(v_00_u03b1_1644_, v_cs_1645_, v_k_1646_, v_h_boxed_1649_, v_j_1648_);
lean_dec(v_k_1646_);
lean_dec_ref(v_cs_1645_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_match__1_splitter___redArg(lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v_h__1_1654_, lean_object* v_h__2_1655_, lean_object* v_h__3_1656_){
_start:
{
switch(lean_obj_tag(v_x_1651_))
{
case 0:
{
lean_object* v_modIdx_1657_; lean_object* v_tree_1658_; lean_object* v___x_1659_; 
lean_dec(v_h__3_1656_);
lean_dec(v_h__2_1655_);
v_modIdx_1657_ = lean_ctor_get(v_x_1651_, 0);
lean_inc(v_modIdx_1657_);
v_tree_1658_ = lean_ctor_get(v_x_1651_, 1);
lean_inc_ref(v_tree_1658_);
lean_dec_ref_known(v_x_1651_, 2);
v___x_1659_ = lean_apply_4(v_h__1_1654_, v_modIdx_1657_, v_tree_1658_, v_x_1652_, v_x_1653_);
return v___x_1659_;
}
case 1:
{
lean_object* v_key_1660_; lean_object* v_entry_x3f_1661_; lean_object* v_children_1662_; lean_object* v___x_1663_; 
lean_dec(v_h__2_1655_);
lean_dec(v_h__1_1654_);
v_key_1660_ = lean_ctor_get(v_x_1651_, 0);
lean_inc(v_key_1660_);
v_entry_x3f_1661_ = lean_ctor_get(v_x_1651_, 1);
lean_inc(v_entry_x3f_1661_);
v_children_1662_ = lean_ctor_get(v_x_1651_, 2);
lean_inc_ref(v_children_1662_);
lean_dec_ref_known(v_x_1651_, 3);
v___x_1663_ = lean_apply_5(v_h__3_1656_, v_key_1660_, v_entry_x3f_1661_, v_children_1662_, v_x_1652_, v_x_1653_);
return v___x_1663_;
}
default: 
{
lean_object* v_key_1664_; lean_object* v_entry_x3f_1665_; lean_object* v_children_1666_; lean_object* v___x_1667_; 
lean_dec(v_h__3_1656_);
lean_dec(v_h__1_1654_);
v_key_1664_ = lean_ctor_get(v_x_1651_, 0);
lean_inc(v_key_1664_);
v_entry_x3f_1665_ = lean_ctor_get(v_x_1651_, 1);
lean_inc(v_entry_x3f_1665_);
v_children_1666_ = lean_ctor_get(v_x_1651_, 2);
lean_inc_ref(v_children_1666_);
lean_dec_ref_known(v_x_1651_, 3);
v___x_1667_ = lean_apply_5(v_h__2_1655_, v_key_1664_, v_entry_x3f_1665_, v_children_1666_, v_x_1652_, v_x_1653_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_match__1_splitter(lean_object* v_00_u03b1_1668_, lean_object* v_motive_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_h__1_1673_, lean_object* v_h__2_1674_, lean_object* v_h__3_1675_){
_start:
{
switch(lean_obj_tag(v_x_1670_))
{
case 0:
{
lean_object* v_modIdx_1676_; lean_object* v_tree_1677_; lean_object* v___x_1678_; 
lean_dec(v_h__3_1675_);
lean_dec(v_h__2_1674_);
v_modIdx_1676_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_modIdx_1676_);
v_tree_1677_ = lean_ctor_get(v_x_1670_, 1);
lean_inc_ref(v_tree_1677_);
lean_dec_ref_known(v_x_1670_, 2);
v___x_1678_ = lean_apply_4(v_h__1_1673_, v_modIdx_1676_, v_tree_1677_, v_x_1671_, v_x_1672_);
return v___x_1678_;
}
case 1:
{
lean_object* v_key_1679_; lean_object* v_entry_x3f_1680_; lean_object* v_children_1681_; lean_object* v___x_1682_; 
lean_dec(v_h__2_1674_);
lean_dec(v_h__1_1673_);
v_key_1679_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_key_1679_);
v_entry_x3f_1680_ = lean_ctor_get(v_x_1670_, 1);
lean_inc(v_entry_x3f_1680_);
v_children_1681_ = lean_ctor_get(v_x_1670_, 2);
lean_inc_ref(v_children_1681_);
lean_dec_ref_known(v_x_1670_, 3);
v___x_1682_ = lean_apply_5(v_h__3_1675_, v_key_1679_, v_entry_x3f_1680_, v_children_1681_, v_x_1671_, v_x_1672_);
return v___x_1682_;
}
default: 
{
lean_object* v_key_1683_; lean_object* v_entry_x3f_1684_; lean_object* v_children_1685_; lean_object* v___x_1686_; 
lean_dec(v_h__3_1675_);
lean_dec(v_h__1_1673_);
v_key_1683_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_key_1683_);
v_entry_x3f_1684_ = lean_ctor_get(v_x_1670_, 1);
lean_inc(v_entry_x3f_1684_);
v_children_1685_ = lean_ctor_get(v_x_1670_, 2);
lean_inc_ref(v_children_1685_);
lean_dec_ref_known(v_x_1670_, 3);
v___x_1686_ = lean_apply_5(v_h__2_1674_, v_key_1683_, v_entry_x3f_1684_, v_children_1685_, v_x_1671_, v_x_1672_);
return v___x_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg(lean_object* v_x_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_obj_once(&l_Lean_instInhabitedImportedTree___closed__0, &l_Lean_instInhabitedImportedTree___closed__0_once, _init_l_Lean_instInhabitedImportedTree___closed__0);
switch(lean_obj_tag(v_x_1687_))
{
case 0:
{
lean_object* v_modIdx_1692_; lean_object* v_tree_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1710_; 
v_modIdx_1692_ = lean_ctor_get(v_x_1687_, 0);
v_tree_1693_ = lean_ctor_get(v_x_1687_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1695_ = v_x_1687_;
v_isShared_1696_ = v_isSharedCheck_1710_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_tree_1693_);
lean_inc(v_modIdx_1692_);
lean_dec(v_x_1687_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1710_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Lean_ConstTrie_0__Lean_ConstTrie_findAux___redArg(v_tree_1693_, v_x_1688_, v_x_1689_);
lean_dec_ref(v_tree_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v___x_1698_; 
lean_del_object(v___x_1695_);
lean_dec(v_modIdx_1692_);
v___x_1698_ = lean_box(0);
return v___x_1698_;
}
else
{
lean_object* v_val_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1709_; 
v_val_1699_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1701_ = v___x_1697_;
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_val_1699_);
lean_dec(v___x_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 1, v_modIdx_1692_);
lean_ctor_set(v___x_1695_, 0, v_val_1699_);
v___x_1704_ = v___x_1695_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_val_1699_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_modIdx_1692_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
case 1:
{
lean_object* v_entry_x3f_1711_; lean_object* v_children_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_entry_x3f_1711_ = lean_ctor_get(v_x_1687_, 1);
lean_inc(v_entry_x3f_1711_);
v_children_1712_ = lean_ctor_get(v_x_1687_, 2);
lean_inc_ref(v_children_1712_);
lean_dec_ref_known(v_x_1687_, 3);
v___x_1713_ = lean_unsigned_to_nat(0u);
v___x_1714_ = lean_nat_dec_eq(v_x_1689_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v_entry_x3f_1711_);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_nat_sub(v_x_1689_, v___x_1715_);
lean_dec(v_x_1689_);
v___x_1717_ = lean_array_get_borrowed(v___x_1690_, v_x_1688_, v___x_1716_);
v___x_1718_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(v_children_1712_, v___x_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; 
lean_dec(v___x_1716_);
lean_dec_ref(v_children_1712_);
v___x_1719_ = lean_box(0);
return v___x_1719_;
}
else
{
lean_object* v_val_1720_; lean_object* v___x_1721_; 
v_val_1720_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1721_ = lean_array_get(v___x_1691_, v_children_1712_, v_val_1720_);
lean_dec(v_val_1720_);
lean_dec_ref(v_children_1712_);
v_x_1687_ = v___x_1721_;
v_x_1689_ = v___x_1716_;
goto _start;
}
}
else
{
lean_dec_ref(v_children_1712_);
lean_dec(v_x_1689_);
return v_entry_x3f_1711_;
}
}
default: 
{
lean_object* v_entry_x3f_1723_; lean_object* v_children_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_entry_x3f_1723_ = lean_ctor_get(v_x_1687_, 1);
lean_inc(v_entry_x3f_1723_);
v_children_1724_ = lean_ctor_get(v_x_1687_, 2);
lean_inc_ref(v_children_1724_);
lean_dec_ref_known(v_x_1687_, 3);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_nat_dec_eq(v_x_1689_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v_cs_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_entry_x3f_1723_);
v_cs_1727_ = lean_thunk_get_own(v_children_1724_);
lean_dec_ref(v_children_1724_);
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_sub(v_x_1689_, v___x_1728_);
lean_dec(v_x_1689_);
v___x_1730_ = lean_array_get_borrowed(v___x_1690_, v_x_1688_, v___x_1729_);
v___x_1731_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux_spec__0___redArg(v_cs_1727_, v___x_1730_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; 
lean_dec(v___x_1729_);
lean_dec(v_cs_1727_);
v___x_1732_ = lean_box(0);
return v___x_1732_;
}
else
{
lean_object* v_val_1733_; lean_object* v___x_1734_; 
v_val_1733_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1734_ = lean_array_get(v___x_1691_, v_cs_1727_, v_val_1733_);
lean_dec(v_val_1733_);
lean_dec(v_cs_1727_);
v_x_1687_ = v___x_1734_;
v_x_1689_ = v___x_1729_;
goto _start;
}
}
else
{
lean_dec_ref(v_children_1724_);
lean_dec(v_x_1689_);
return v_entry_x3f_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg___boxed(lean_object* v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg(v_x_1736_, v_x_1737_, v_x_1738_);
lean_dec_ref(v_x_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux(lean_object* v_00_u03b1_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg(v_x_1741_, v_x_1742_, v_x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux(v_00_u03b1_1745_, v_x_1746_, v_x_1747_, v_x_1748_);
lean_dec_ref(v_x_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_empty___redArg(){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_Lean_instInhabitedImportedConsts___redArg___closed__1));
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_empty___redArg___boxed(lean_object* v___dummy_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_ImportedConsts_empty___redArg();
return v_res_1753_;
}
}
static lean_object* _init_l_Lean_ImportedConsts_empty___closed__0(void){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_ImportedConsts_empty___redArg();
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_empty(lean_object* v_00_u03b1_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_obj_once(&l_Lean_ImportedConsts_empty___closed__0, &l_Lean_ImportedConsts_empty___closed__0_once, _init_l_Lean_ImportedConsts_empty___closed__0);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache___redArg(lean_object* v_t_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_tree_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v___x_1759_ = lean_imported_consts_cache_new();
v_tree_1760_ = lean_ctor_get(v_t_1757_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_t_1757_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_t_1757_, 0);
lean_dec(v_unused_1769_);
v___x_1762_ = v_t_1757_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_tree_1760_);
lean_dec(v_t_1757_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1759_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_tree_1760_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache___redArg___boxed(lean_object* v_t_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_ImportedConsts_withCache___redArg(v_t_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache(lean_object* v_00_u03b1_1773_, lean_object* v_t_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_ImportedConsts_withCache___redArg(v_t_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_withCache___boxed(lean_object* v_00_u03b1_1777_, lean_object* v_t_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_ImportedConsts_withCache(v_00_u03b1_1777_, v_t_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findEntry_x3f___redArg(lean_object* v_t_1781_, lean_object* v_n_1782_){
_start:
{
lean_object* v_tree_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v_path_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_tree_1783_ = lean_ctor_get(v_t_1781_, 1);
lean_inc_ref(v_tree_1783_);
lean_dec_ref(v_t_1781_);
v___x_1784_ = lean_unsigned_to_nat(8u);
v___x_1785_ = lean_mk_empty_array_with_capacity(v___x_1784_);
v_path_1786_ = l___private_Lean_ConstTrie_0__Lean_prefixesOf(v_n_1782_, v___x_1785_);
v___x_1787_ = lean_array_get_size(v_path_1786_);
v___x_1788_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findEntryAux___redArg(v_tree_1783_, v_path_1786_, v___x_1787_);
lean_dec_ref(v_path_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findEntry_x3f(lean_object* v_00_u03b1_1789_, lean_object* v_t_1790_, lean_object* v_n_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_ImportedConsts_findEntry_x3f___redArg(v_t_1790_, v_n_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* lean_imported_extra_consts_find_entry_core(lean_object* v_t_1793_, lean_object* v_n_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_ImportedConsts_findEntry_x3f___redArg(v_t_1793_, v_n_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_findExtraEntryCachedImpl___boxed(lean_object* v_cache_x3f_1799_, lean_object* v_t_1800_, lean_object* v_n_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = lean_imported_extra_consts_find_entry_cached(v_cache_x3f_1799_, v_t_1800_, v_n_1801_);
lean_dec(v_n_1801_);
lean_dec_ref(v_t_1800_);
lean_dec(v_cache_x3f_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraEntryCached_x3f(lean_object* v_t_1803_, lean_object* v_n_1804_){
_start:
{
lean_object* v_cache_x3f_1805_; lean_object* v___x_1806_; 
v_cache_x3f_1805_ = lean_ctor_get(v_t_1803_, 0);
v___x_1806_ = lean_imported_extra_consts_find_entry_cached(v_cache_x3f_1805_, v_t_1803_, v_n_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraEntryCached_x3f___boxed(lean_object* v_t_1807_, lean_object* v_n_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_ImportedConsts_findExtraEntryCached_x3f(v_t_1807_, v_n_1808_);
lean_dec(v_n_1808_);
lean_dec_ref(v_t_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_findExtraModIdxCachedImpl___boxed(lean_object* v_cache_x3f_1813_, lean_object* v_t_1814_, lean_object* v_n_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = lean_imported_extra_consts_find_mod_idx_cached(v_cache_x3f_1813_, v_t_1814_, v_n_1815_);
lean_dec(v_n_1815_);
lean_dec_ref(v_t_1814_);
lean_dec(v_cache_x3f_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraModIdxCached_x3f(lean_object* v_t_1817_, lean_object* v_n_1818_){
_start:
{
lean_object* v_cache_x3f_1819_; lean_object* v___x_1820_; lean_object* v_zero_1821_; uint8_t v_isZero_1822_; 
v_cache_x3f_1819_ = lean_ctor_get(v_t_1817_, 0);
v___x_1820_ = lean_imported_extra_consts_find_mod_idx_cached(v_cache_x3f_1819_, v_t_1817_, v_n_1818_);
v_zero_1821_ = lean_unsigned_to_nat(0u);
v_isZero_1822_ = lean_nat_dec_eq(v___x_1820_, v_zero_1821_);
if (v_isZero_1822_ == 1)
{
lean_object* v___x_1823_; 
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
return v___x_1823_;
}
else
{
lean_object* v_one_1824_; lean_object* v_n_1825_; lean_object* v___x_1826_; 
v_one_1824_ = lean_unsigned_to_nat(1u);
v_n_1825_ = lean_nat_sub(v___x_1820_, v_one_1824_);
lean_dec(v___x_1820_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_n_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findExtraModIdxCached_x3f___boxed(lean_object* v_t_1827_, lean_object* v_n_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_ImportedConsts_findExtraModIdxCached_x3f(v_t_1827_, v_n_1828_);
lean_dec(v_n_1828_);
lean_dec_ref(v_t_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_find_x3f___redArg(lean_object* v_t_1830_, lean_object* v_n_1831_){
_start:
{
lean_object* v_tree_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_path_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_tree_1832_ = lean_ctor_get(v_t_1830_, 1);
lean_inc_ref(v_tree_1832_);
lean_dec_ref(v_t_1830_);
v___x_1833_ = lean_unsigned_to_nat(8u);
v___x_1834_ = lean_mk_empty_array_with_capacity(v___x_1833_);
v_path_1835_ = l___private_Lean_ConstTrie_0__Lean_prefixesOf(v_n_1831_, v___x_1834_);
v___x_1836_ = lean_array_get_size(v_path_1835_);
v___x_1837_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_findValAux___redArg(v_tree_1832_, v_path_1835_, v___x_1836_);
lean_dec_ref(v_path_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_find_x3f(lean_object* v_00_u03b1_1838_, lean_object* v_t_1839_, lean_object* v_n_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_ImportedConsts_find_x3f___redArg(v_t_1839_, v_n_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_obj_once(&l_Lean_instInhabitedConstTrie___closed__0, &l_Lean_instInhabitedConstTrie___closed__0_once, _init_l_Lean_instInhabitedConstTrie___closed__0);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg(lean_object* v_single_1845_, lean_object* v_multi_1846_, lean_object* v_groups_1847_, lean_object* v_k_1848_, lean_object* v_s_1849_){
_start:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_array_get_size(v_groups_1847_);
v___x_1851_ = lean_nat_dec_lt(v_k_1848_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec(v_k_1848_);
lean_dec(v_multi_1846_);
lean_dec(v_single_1845_);
return v_s_1849_;
}
else
{
lean_object* v_g_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_g_1852_ = lean_array_fget_borrowed(v_groups_1847_, v_k_1848_);
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_add(v_k_1848_, v___x_1853_);
lean_dec(v_k_1848_);
v___x_1855_ = lean_array_get_size(v_g_1852_);
v___x_1856_ = lean_nat_dec_eq(v___x_1855_, v___x_1853_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_inc(v_multi_1846_);
lean_inc(v_g_1852_);
v___x_1857_ = lean_apply_4(v_multi_1846_, v_s_1849_, v_g_1852_, lean_box(0), lean_box(0));
v_k_1848_ = v___x_1854_;
v_s_1849_ = v___x_1857_;
goto _start;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_obj_once(&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0, &l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0_once, _init_l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0);
v___x_1861_ = lean_array_get_borrowed(v___x_1860_, v_g_1852_, v___x_1859_);
v_fst_1862_ = lean_ctor_get(v___x_1861_, 0);
v_snd_1863_ = lean_ctor_get(v___x_1861_, 1);
lean_inc(v_single_1845_);
lean_inc(v_snd_1863_);
lean_inc(v_fst_1862_);
v___x_1864_ = lean_apply_3(v_single_1845_, v_s_1849_, v_fst_1862_, v_snd_1863_);
v_k_1848_ = v___x_1854_;
v_s_1849_ = v___x_1864_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___boxed(lean_object* v_single_1866_, lean_object* v_multi_1867_, lean_object* v_groups_1868_, lean_object* v_k_1869_, lean_object* v_s_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg(v_single_1866_, v_multi_1867_, v_groups_1868_, v_k_1869_, v_s_1870_);
lean_dec_ref(v_groups_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush(lean_object* v_00_u03b1_1872_, lean_object* v_00_u03c3_1873_, lean_object* v_cands_1874_, lean_object* v_single_1875_, lean_object* v_multi_1876_, lean_object* v_groups_1877_, lean_object* v_hgroups_1878_, lean_object* v_k_1879_, lean_object* v_s_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg(v_single_1875_, v_multi_1876_, v_groups_1877_, v_k_1879_, v_s_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_00_u03c3_1883_, lean_object* v_cands_1884_, lean_object* v_single_1885_, lean_object* v_multi_1886_, lean_object* v_groups_1887_, lean_object* v_hgroups_1888_, lean_object* v_k_1889_, lean_object* v_s_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush(v_00_u03b1_1882_, v_00_u03c3_1883_, v_cands_1884_, v_single_1885_, v_multi_1886_, v_groups_1887_, v_hgroups_1888_, v_k_1889_, v_s_1890_);
lean_dec_ref(v_groups_1887_);
lean_dec_ref(v_cands_1884_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg(uint64_t v___x_1892_, uint64_t v_hash_u2080_1893_, lean_object* v_snd_1894_, lean_object* v_as_1895_, lean_object* v_j_1896_){
_start:
{
uint8_t v___y_1902_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_array_get_size(v_as_1895_);
v___x_1905_ = lean_nat_dec_lt(v_j_1896_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec(v_j_1896_);
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_snd_1911_; uint8_t v___x_1912_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1923_; lean_object* v_key_1925_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_obj_once(&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0, &l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0_once, _init_l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0);
v___x_1909_ = lean_array_fget_borrowed(v_as_1895_, v_j_1896_);
v___x_1910_ = lean_array_get_borrowed(v___x_1908_, v___x_1909_, v___x_1907_);
v_snd_1911_ = lean_ctor_get(v___x_1910_, 1);
v___x_1912_ = lean_uint64_dec_eq(v___x_1892_, v_hash_u2080_1893_);
v_key_1925_ = lean_ctor_get(v_snd_1911_, 0);
v___y_1923_ = v_key_1925_;
goto v___jp_1922_;
v___jp_1913_:
{
switch(lean_obj_tag(v___y_1914_))
{
case 0:
{
if (lean_obj_tag(v___y_1915_) == 0)
{
v___y_1902_ = v___x_1912_;
goto v___jp_1901_;
}
else
{
goto v___jp_1897_;
}
}
case 1:
{
if (lean_obj_tag(v___y_1915_) == 1)
{
lean_object* v_str_1916_; lean_object* v_str_1917_; uint8_t v___x_1918_; 
v_str_1916_ = lean_ctor_get(v___y_1914_, 1);
v_str_1917_ = lean_ctor_get(v___y_1915_, 1);
v___x_1918_ = lean_string_dec_eq(v_str_1916_, v_str_1917_);
v___y_1902_ = v___x_1918_;
goto v___jp_1901_;
}
else
{
goto v___jp_1897_;
}
}
default: 
{
if (lean_obj_tag(v___y_1915_) == 2)
{
lean_object* v_i_1919_; lean_object* v_i_1920_; uint8_t v___x_1921_; 
v_i_1919_ = lean_ctor_get(v___y_1914_, 1);
v_i_1920_ = lean_ctor_get(v___y_1915_, 1);
v___x_1921_ = lean_nat_dec_eq(v_i_1919_, v_i_1920_);
v___y_1902_ = v___x_1921_;
goto v___jp_1901_;
}
else
{
goto v___jp_1897_;
}
}
}
}
v___jp_1922_:
{
lean_object* v_key_1924_; 
v_key_1924_ = lean_ctor_get(v_snd_1894_, 0);
v___y_1914_ = v___y_1923_;
v___y_1915_ = v_key_1924_;
goto v___jp_1913_;
}
}
v___jp_1897_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_add(v_j_1896_, v___x_1898_);
lean_dec(v_j_1896_);
v_j_1896_ = v___x_1899_;
goto _start;
}
v___jp_1901_:
{
if (v___y_1902_ == 0)
{
goto v___jp_1897_;
}
else
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_j_1896_);
return v___x_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg___boxed(lean_object* v___x_1926_, lean_object* v_hash_u2080_1927_, lean_object* v_snd_1928_, lean_object* v_as_1929_, lean_object* v_j_1930_){
_start:
{
uint64_t v___x_488__boxed_1931_; uint64_t v_hash_u2080_boxed_1932_; lean_object* v_res_1933_; 
v___x_488__boxed_1931_ = lean_unbox_uint64(v___x_1926_);
lean_dec_ref(v___x_1926_);
v_hash_u2080_boxed_1932_ = lean_unbox_uint64(v_hash_u2080_1927_);
lean_dec_ref(v_hash_u2080_1927_);
v_res_1933_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg(v___x_488__boxed_1931_, v_hash_u2080_boxed_1932_, v_snd_1928_, v_as_1929_, v_j_1930_);
lean_dec_ref(v_as_1929_);
lean_dec_ref(v_snd_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(lean_object* v_sorted_1934_, uint64_t v_hash_u2080_1935_, lean_object* v_idx_1936_, lean_object* v_groups_1937_){
_start:
{
lean_object* v_val_1939_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = lean_array_get_size(v_sorted_1934_);
v___x_1944_ = lean_nat_dec_lt(v_idx_1936_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_groups_1937_);
lean_ctor_set(v___x_1945_, 1, v_idx_1936_);
return v___x_1945_;
}
else
{
lean_object* v___x_1946_; lean_object* v_fst_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1984_; 
v___x_1946_ = lean_array_fget(v_sorted_1934_, v_idx_1936_);
v_fst_1947_ = lean_ctor_get(v___x_1946_, 0);
v_snd_1948_ = lean_ctor_get(v___x_1946_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1984_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_inc(v_fst_1947_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1984_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
uint64_t v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = lean_unbox_uint64(v_fst_1947_);
v___x_1953_ = lean_uint64_dec_eq(v___x_1952_, v_hash_u2080_1935_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1955_; 
lean_dec(v_snd_1948_);
lean_dec(v_fst_1947_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_idx_1936_);
lean_ctor_set(v___x_1950_, 0, v_groups_1937_);
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_groups_1937_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_idx_1936_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
else
{
lean_object* v_fst_1957_; lean_object* v_snd_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1983_; 
lean_del_object(v___x_1950_);
v_fst_1957_ = lean_ctor_get(v_snd_1948_, 0);
v_snd_1958_ = lean_ctor_get(v_snd_1948_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_snd_1948_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1960_ = v_snd_1948_;
v_isShared_1961_ = v_isSharedCheck_1983_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snd_1958_);
lean_inc(v_fst_1957_);
lean_dec(v_snd_1948_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1983_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; uint64_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_unbox_uint64(v_fst_1947_);
lean_dec(v_fst_1947_);
v___x_1964_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg(v___x_1963_, v_hash_u2080_1935_, v_snd_1958_, v_groups_1937_, v___x_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1966_; 
if (v_isShared_1961_ == 0)
{
v___x_1966_ = v___x_1960_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_fst_1957_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_snd_1958_);
v___x_1966_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_mk_empty_array_with_capacity(v___x_1967_);
v___x_1969_ = lean_array_push(v___x_1968_, v___x_1966_);
v___x_1970_ = lean_array_push(v_groups_1937_, v___x_1969_);
v_val_1939_ = v___x_1970_;
goto v___jp_1938_;
}
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_val_1972_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1973_ = lean_array_get_size(v_groups_1937_);
v___x_1974_ = lean_nat_dec_lt(v_val_1972_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_dec(v_val_1972_);
lean_del_object(v___x_1960_);
lean_dec(v_snd_1958_);
lean_dec(v_fst_1957_);
v_val_1939_ = v_groups_1937_;
goto v___jp_1938_;
}
else
{
lean_object* v_v_1975_; lean_object* v___x_1976_; lean_object* v_xs_x27_1977_; lean_object* v___x_1979_; 
v_v_1975_ = lean_array_fget(v_groups_1937_, v_val_1972_);
v___x_1976_ = lean_box(0);
v_xs_x27_1977_ = lean_array_fset(v_groups_1937_, v_val_1972_, v___x_1976_);
if (v_isShared_1961_ == 0)
{
v___x_1979_ = v___x_1960_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_fst_1957_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_snd_1958_);
v___x_1979_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_array_push(v_v_1975_, v___x_1979_);
v___x_1981_ = lean_array_fset(v_xs_x27_1977_, v_val_1972_, v___x_1980_);
lean_dec(v_val_1972_);
v_val_1939_ = v___x_1981_;
goto v___jp_1938_;
}
}
}
}
}
}
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_add(v_idx_1936_, v___x_1940_);
lean_dec(v_idx_1936_);
v_idx_1936_ = v___x_1941_;
v_groups_1937_ = v_val_1939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg___boxed(lean_object* v_sorted_1985_, lean_object* v_hash_u2080_1986_, lean_object* v_idx_1987_, lean_object* v_groups_1988_){
_start:
{
uint64_t v_hash_u2080_boxed_1989_; lean_object* v_res_1990_; 
v_hash_u2080_boxed_1989_ = lean_unbox_uint64(v_hash_u2080_1986_);
lean_dec_ref(v_hash_u2080_1986_);
v_res_1990_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(v_sorted_1985_, v_hash_u2080_boxed_1989_, v_idx_1987_, v_groups_1988_);
lean_dec_ref(v_sorted_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather(lean_object* v_00_u03b1_1991_, lean_object* v_cands_1992_, lean_object* v_sorted_1993_, uint64_t v_hash_u2080_1994_, lean_object* v_idx_1995_, lean_object* v_groups_1996_, lean_object* v_hgroups_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(v_sorted_1993_, v_hash_u2080_1994_, v_idx_1995_, v_groups_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_cands_2000_, lean_object* v_sorted_2001_, lean_object* v_hash_u2080_2002_, lean_object* v_idx_2003_, lean_object* v_groups_2004_, lean_object* v_hgroups_2005_){
_start:
{
uint64_t v_hash_u2080_boxed_2006_; lean_object* v_res_2007_; 
v_hash_u2080_boxed_2006_ = lean_unbox_uint64(v_hash_u2080_2002_);
lean_dec_ref(v_hash_u2080_2002_);
v_res_2007_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather(v_00_u03b1_1999_, v_cands_2000_, v_sorted_2001_, v_hash_u2080_boxed_2006_, v_idx_2003_, v_groups_2004_, v_hgroups_2005_);
lean_dec_ref(v_sorted_2001_);
lean_dec_ref(v_cands_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0(lean_object* v_00_u03b1_2008_, uint64_t v___x_2009_, uint64_t v_hash_u2080_2010_, lean_object* v_snd_2011_, lean_object* v_as_2012_, lean_object* v_j_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___redArg(v___x_2009_, v_hash_u2080_2010_, v_snd_2011_, v_as_2012_, v_j_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0___boxed(lean_object* v_00_u03b1_2015_, lean_object* v___x_2016_, lean_object* v_hash_u2080_2017_, lean_object* v_snd_2018_, lean_object* v_as_2019_, lean_object* v_j_2020_){
_start:
{
uint64_t v___x_653__boxed_2021_; uint64_t v_hash_u2080_boxed_2022_; lean_object* v_res_2023_; 
v___x_653__boxed_2021_ = lean_unbox_uint64(v___x_2016_);
lean_dec_ref(v___x_2016_);
v_hash_u2080_boxed_2022_ = lean_unbox_uint64(v_hash_u2080_2017_);
lean_dec_ref(v_hash_u2080_2017_);
v_res_2023_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_spec__0(v_00_u03b1_2015_, v___x_653__boxed_2021_, v_hash_u2080_boxed_2022_, v_snd_2018_, v_as_2019_, v_j_2020_);
lean_dec_ref(v_as_2019_);
lean_dec_ref(v_snd_2018_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter___redArg(lean_object* v_x_2024_, lean_object* v_h__1_2025_){
_start:
{
lean_object* v_snd_2026_; lean_object* v_fst_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; 
v_snd_2026_ = lean_ctor_get(v_x_2024_, 1);
lean_inc(v_snd_2026_);
v_fst_2027_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_fst_2027_);
lean_dec_ref(v_x_2024_);
v_fst_2028_ = lean_ctor_get(v_snd_2026_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v_snd_2026_, 1);
lean_inc(v_snd_2029_);
lean_dec(v_snd_2026_);
v___x_2030_ = lean_apply_3(v_h__1_2025_, v_fst_2027_, v_fst_2028_, v_snd_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter(lean_object* v_00_u03b1_2031_, lean_object* v_cands_2032_, lean_object* v_motive_2033_, lean_object* v_x_2034_, lean_object* v_h__1_2035_){
_start:
{
lean_object* v_snd_2036_; lean_object* v_fst_2037_; lean_object* v_fst_2038_; lean_object* v_snd_2039_; lean_object* v___x_2040_; 
v_snd_2036_ = lean_ctor_get(v_x_2034_, 1);
lean_inc(v_snd_2036_);
v_fst_2037_ = lean_ctor_get(v_x_2034_, 0);
lean_inc(v_fst_2037_);
lean_dec_ref(v_x_2034_);
v_fst_2038_ = lean_ctor_get(v_snd_2036_, 0);
lean_inc(v_fst_2038_);
v_snd_2039_ = lean_ctor_get(v_snd_2036_, 1);
lean_inc(v_snd_2039_);
lean_dec(v_snd_2036_);
v___x_2040_ = lean_apply_3(v_h__1_2035_, v_fst_2037_, v_fst_2038_, v_snd_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_cands_2042_, lean_object* v_motive_2043_, lean_object* v_x_2044_, lean_object* v_h__1_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__3_splitter(v_00_u03b1_2041_, v_cands_2042_, v_motive_2043_, v_x_2044_, v_h__1_2045_);
lean_dec_ref(v_cands_2042_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter___redArg(lean_object* v_x_2047_, lean_object* v_h__1_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_apply_2(v_h__1_2048_, v_x_2047_, lean_box(0));
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter(lean_object* v_00_u03b1_2050_, lean_object* v_cands_2051_, lean_object* v_motive_2052_, lean_object* v_x_2053_, lean_object* v_h__1_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_apply_2(v_h__1_2054_, v_x_2053_, lean_box(0));
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_cands_2057_, lean_object* v_motive_2058_, lean_object* v_x_2059_, lean_object* v_h__1_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__3_splitter(v_00_u03b1_2056_, v_cands_2057_, v_motive_2058_, v_x_2059_, v_h__1_2060_);
lean_dec_ref(v_cands_2057_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter___redArg(lean_object* v_x_2062_, lean_object* v_h__1_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_apply_3(v_h__1_2063_, v_x_2062_, lean_box(0), lean_box(0));
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter(lean_object* v_00_u03b1_2065_, lean_object* v_cands_2066_, lean_object* v_idx_2067_, lean_object* v_motive_2068_, lean_object* v_x_2069_, lean_object* v_h__1_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_apply_3(v_h__1_2070_, v_x_2069_, lean_box(0), lean_box(0));
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_cands_2073_, lean_object* v_idx_2074_, lean_object* v_motive_2075_, lean_object* v_x_2076_, lean_object* v_h__1_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather_match__1_splitter(v_00_u03b1_2072_, v_cands_2073_, v_idx_2074_, v_motive_2075_, v_x_2076_, v_h__1_2077_);
lean_dec(v_idx_2074_);
lean_dec_ref(v_cands_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(lean_object* v_single_2079_, lean_object* v_multi_2080_, lean_object* v_sorted_2081_, lean_object* v_idx_2082_, lean_object* v_s_2083_){
_start:
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = lean_array_get_size(v_sorted_2081_);
v___x_2085_ = lean_nat_dec_lt(v_idx_2082_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec(v_idx_2082_);
lean_dec(v_multi_2080_);
lean_dec(v_single_2079_);
return v_s_2083_;
}
else
{
lean_object* v___x_2086_; lean_object* v_snd_2087_; lean_object* v_fst_2088_; lean_object* v_fst_2089_; lean_object* v_snd_2090_; lean_object* v___x_2091_; lean_object* v_idx_2092_; uint8_t v___x_2093_; 
v___x_2086_ = lean_array_fget_borrowed(v_sorted_2081_, v_idx_2082_);
v_snd_2087_ = lean_ctor_get(v___x_2086_, 1);
v_fst_2088_ = lean_ctor_get(v___x_2086_, 0);
v_fst_2089_ = lean_ctor_get(v_snd_2087_, 0);
v_snd_2090_ = lean_ctor_get(v_snd_2087_, 1);
v___x_2091_ = lean_unsigned_to_nat(1u);
v_idx_2092_ = lean_nat_add(v_idx_2082_, v___x_2091_);
lean_dec(v_idx_2082_);
v___x_2093_ = lean_nat_dec_lt(v_idx_2092_, v___x_2084_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_inc(v_single_2079_);
lean_inc(v_snd_2090_);
lean_inc(v_fst_2089_);
v___x_2094_ = lean_apply_3(v_single_2079_, v_s_2083_, v_fst_2089_, v_snd_2090_);
v_idx_2082_ = v_idx_2092_;
v_s_2083_ = v___x_2094_;
goto _start;
}
else
{
lean_object* v___x_2096_; lean_object* v_fst_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2119_; 
v___x_2096_ = lean_array_fget(v_sorted_2081_, v_idx_2092_);
v_fst_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v___x_2096_, 1);
lean_dec(v_unused_2120_);
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2119_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_fst_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2119_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint64_t v___x_2101_; uint64_t v___x_2102_; uint8_t v___x_2103_; 
v___x_2101_ = lean_unbox_uint64(v_fst_2097_);
lean_dec(v_fst_2097_);
v___x_2102_ = lean_unbox_uint64(v_fst_2088_);
v___x_2103_ = lean_uint64_dec_eq(v___x_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_del_object(v___x_2099_);
lean_inc(v_single_2079_);
lean_inc(v_snd_2090_);
lean_inc(v_fst_2089_);
v___x_2104_ = lean_apply_3(v_single_2079_, v_s_2083_, v_fst_2089_, v_snd_2090_);
v_idx_2082_ = v_idx_2092_;
v_s_2083_ = v___x_2104_;
goto _start;
}
else
{
lean_object* v___x_2107_; 
lean_inc(v_snd_2090_);
lean_inc(v_fst_2089_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v_snd_2090_);
lean_ctor_set(v___x_2099_, 0, v_fst_2089_);
v___x_2107_ = v___x_2099_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_fst_2089_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_snd_2090_);
v___x_2107_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint64_t v___x_2111_; lean_object* v_val_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2108_ = lean_mk_empty_array_with_capacity(v___x_2091_);
lean_inc_ref(v___x_2108_);
v___x_2109_ = lean_array_push(v___x_2108_, v___x_2107_);
v___x_2110_ = lean_array_push(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_unbox_uint64(v_fst_2088_);
v_val_2112_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(v_sorted_2081_, v___x_2111_, v_idx_2092_, v___x_2110_);
v_fst_2113_ = lean_ctor_get(v_val_2112_, 0);
lean_inc(v_fst_2113_);
v_snd_2114_ = lean_ctor_get(v_val_2112_, 1);
lean_inc(v_snd_2114_);
lean_dec_ref(v_val_2112_);
v___x_2115_ = lean_unsigned_to_nat(0u);
lean_inc(v_multi_2080_);
lean_inc(v_single_2079_);
v___x_2116_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg(v_single_2079_, v_multi_2080_, v_fst_2113_, v___x_2115_, v_s_2083_);
lean_dec(v_fst_2113_);
v_idx_2082_ = v_snd_2114_;
v_s_2083_ = v___x_2116_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg___boxed(lean_object* v_single_2121_, lean_object* v_multi_2122_, lean_object* v_sorted_2123_, lean_object* v_idx_2124_, lean_object* v_s_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(v_single_2121_, v_multi_2122_, v_sorted_2123_, v_idx_2124_, v_s_2125_);
lean_dec_ref(v_sorted_2123_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go(lean_object* v_00_u03b1_2127_, lean_object* v_00_u03c3_2128_, lean_object* v_cands_2129_, lean_object* v_single_2130_, lean_object* v_multi_2131_, lean_object* v_sorted_2132_, lean_object* v_idx_2133_, lean_object* v_s_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(v_single_2130_, v_multi_2131_, v_sorted_2132_, v_idx_2133_, v_s_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_00_u03c3_2137_, lean_object* v_cands_2138_, lean_object* v_single_2139_, lean_object* v_multi_2140_, lean_object* v_sorted_2141_, lean_object* v_idx_2142_, lean_object* v_s_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go(v_00_u03b1_2136_, v_00_u03c3_2137_, v_cands_2138_, v_single_2139_, v_multi_2140_, v_sorted_2141_, v_idx_2142_, v_s_2143_);
lean_dec_ref(v_sorted_2141_);
lean_dec_ref(v_cands_2138_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter___redArg(lean_object* v_x_2145_, lean_object* v_h__1_2146_){
_start:
{
lean_object* v_fst_2147_; lean_object* v_snd_2148_; lean_object* v___x_2149_; 
v_fst_2147_ = lean_ctor_get(v_x_2145_, 0);
lean_inc(v_fst_2147_);
v_snd_2148_ = lean_ctor_get(v_x_2145_, 1);
lean_inc(v_snd_2148_);
lean_dec_ref(v_x_2145_);
v___x_2149_ = lean_apply_4(v_h__1_2146_, v_fst_2147_, v_snd_2148_, lean_box(0), lean_box(0));
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter(lean_object* v_00_u03b1_2150_, lean_object* v_cands_2151_, lean_object* v_idx_2152_, lean_object* v_motive_2153_, lean_object* v_x_2154_, lean_object* v_h__1_2155_){
_start:
{
lean_object* v_fst_2156_; lean_object* v_snd_2157_; lean_object* v___x_2158_; 
v_fst_2156_ = lean_ctor_get(v_x_2154_, 0);
lean_inc(v_fst_2156_);
v_snd_2157_ = lean_ctor_get(v_x_2154_, 1);
lean_inc(v_snd_2157_);
lean_dec_ref(v_x_2154_);
v___x_2158_ = lean_apply_4(v_h__1_2155_, v_fst_2156_, v_snd_2157_, lean_box(0), lean_box(0));
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter___boxed(lean_object* v_00_u03b1_2159_, lean_object* v_cands_2160_, lean_object* v_idx_2161_, lean_object* v_motive_2162_, lean_object* v_x_2163_, lean_object* v_h__1_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go_match__1_splitter(v_00_u03b1_2159_, v_cands_2160_, v_idx_2161_, v_motive_2162_, v_x_2163_, v_h__1_2164_);
lean_dec(v_idx_2161_);
lean_dec_ref(v_cands_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__0(lean_object* v_a_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___y_2170_; lean_object* v_snd_2174_; 
v_snd_2174_ = lean_ctor_get(v_a_2166_, 1);
switch(lean_obj_tag(v_snd_2174_))
{
case 0:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
v___y_2170_ = v___x_2175_;
goto v___jp_2169_;
}
case 1:
{
lean_object* v_children_2176_; 
v_children_2176_ = lean_ctor_get(v_snd_2174_, 1);
v___y_2170_ = v_children_2176_;
goto v___jp_2169_;
}
default: 
{
lean_object* v_children_2177_; 
v_children_2177_ = lean_ctor_get(v_snd_2174_, 2);
v___y_2170_ = v_children_2177_;
goto v___jp_2169_;
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_array_get_size(v___y_2170_);
v___x_2172_ = lean_nat_add(v___y_2168_, v___x_2171_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__0___boxed(lean_object* v_a_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__0(v_a_2178_, v_x_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v_a_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__1(lean_object* v_fst_2182_, lean_object* v_c_2183_, lean_object* v_h_x27_2184_, lean_object* v_____s_2185_){
_start:
{
uint64_t v___y_2187_; lean_object* v___y_2194_; lean_object* v_key_2197_; 
v_key_2197_ = lean_ctor_get(v_c_2183_, 0);
lean_inc(v_key_2197_);
v___y_2194_ = v_key_2197_;
goto v___jp_2193_;
v___jp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_fst_2182_);
lean_ctor_set(v___x_2188_, 1, v_c_2183_);
v___x_2189_ = lean_box_uint64(v___y_2187_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
v___x_2191_ = lean_array_push(v_____s_2185_, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
v___jp_2193_:
{
if (lean_obj_tag(v___y_2194_) == 0)
{
uint64_t v___x_2195_; 
v___x_2195_ = 1723ULL;
v___y_2187_ = v___x_2195_;
goto v___jp_2186_;
}
else
{
uint64_t v_hash_2196_; 
v_hash_2196_ = lean_ctor_get_uint64(v___y_2194_, sizeof(void*)*2);
lean_dec(v___y_2194_);
v___y_2187_ = v_hash_2196_;
goto v___jp_2186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__2(lean_object* v___x_2198_, lean_object* v_p_2199_, lean_object* v_h_2200_, lean_object* v_____s_2201_){
_start:
{
lean_object* v_fst_2202_; lean_object* v_snd_2203_; lean_object* v___f_2204_; lean_object* v___y_2206_; 
v_fst_2202_ = lean_ctor_get(v_p_2199_, 0);
lean_inc(v_fst_2202_);
v_snd_2203_ = lean_ctor_get(v_p_2199_, 1);
lean_inc(v_snd_2203_);
lean_dec_ref(v_p_2199_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__1), 4, 1);
lean_closure_set(v___f_2204_, 0, v_fst_2202_);
switch(lean_obj_tag(v_snd_2203_))
{
case 0:
{
lean_object* v___x_2211_; 
lean_dec_ref_known(v_snd_2203_, 2);
v___x_2211_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
v___y_2206_ = v___x_2211_;
goto v___jp_2205_;
}
case 1:
{
lean_object* v_children_2212_; 
v_children_2212_ = lean_ctor_get(v_snd_2203_, 1);
lean_inc_ref(v_children_2212_);
lean_dec_ref_known(v_snd_2203_, 2);
v___y_2206_ = v_children_2212_;
goto v___jp_2205_;
}
default: 
{
lean_object* v_children_2213_; 
v_children_2213_ = lean_ctor_get(v_snd_2203_, 2);
lean_inc_ref(v_children_2213_);
lean_dec_ref_known(v_snd_2203_, 3);
v___y_2206_ = v_children_2213_;
goto v___jp_2205_;
}
}
v___jp_2205_:
{
size_t v_sz_2207_; size_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_sz_2207_ = lean_array_size(v___y_2206_);
v___x_2208_ = ((size_t)0ULL);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2198_, v___y_2206_, v___f_2204_, v_sz_2207_, v___x_2208_, v_____s_2201_);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3(lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v_snd_2216_; lean_object* v_snd_2217_; lean_object* v_fst_2218_; lean_object* v_fst_2219_; lean_object* v_fst_2220_; lean_object* v_fst_2221_; uint64_t v___x_2222_; uint64_t v___x_2223_; uint8_t v___x_2224_; 
v_snd_2216_ = lean_ctor_get(v_x_2214_, 1);
v_snd_2217_ = lean_ctor_get(v_x_2215_, 1);
v_fst_2218_ = lean_ctor_get(v_x_2214_, 0);
v_fst_2219_ = lean_ctor_get(v_snd_2216_, 0);
v_fst_2220_ = lean_ctor_get(v_x_2215_, 0);
v_fst_2221_ = lean_ctor_get(v_snd_2217_, 0);
v___x_2222_ = lean_unbox_uint64(v_fst_2218_);
v___x_2223_ = lean_unbox_uint64(v_fst_2220_);
v___x_2224_ = lean_uint64_dec_lt(v___x_2222_, v___x_2223_);
if (v___x_2224_ == 0)
{
uint64_t v___x_2225_; uint64_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2225_ = lean_unbox_uint64(v_fst_2218_);
v___x_2226_ = lean_unbox_uint64(v_fst_2220_);
v___x_2227_ = lean_uint64_dec_eq(v___x_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
return v___x_2227_;
}
else
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_nat_dec_lt(v_fst_2219_, v_fst_2221_);
return v___x_2228_;
}
}
else
{
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3___boxed(lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
uint8_t v_res_2231_; lean_object* v_r_2232_; 
v_res_2231_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3(v_x_2229_, v_x_2230_);
lean_dec_ref(v_x_2230_);
lean_dec_ref(v_x_2229_);
v_r_2232_ = lean_box(v_res_2231_);
return v_r_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg(lean_object* v_cands_2256_, lean_object* v_init_2257_, lean_object* v_single_2258_, lean_object* v_multi_2259_){
_start:
{
lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v_total_2263_; size_t v_sz_2264_; size_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___f_2260_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__0));
v___x_2261_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__10));
v___f_2262_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__11));
v_total_2263_ = lean_unsigned_to_nat(0u);
v_sz_2264_ = lean_array_size(v_cands_2256_);
v___x_2265_ = ((size_t)0ULL);
lean_inc_ref(v_cands_2256_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2261_, v_cands_2256_, v___f_2260_, v_sz_2264_, v___x_2265_, v_total_2263_);
v___x_2267_ = lean_mk_empty_array_with_capacity(v___x_2266_);
lean_dec(v___x_2266_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2261_, v_cands_2256_, v___f_2262_, v_sz_2264_, v___x_2265_, v___x_2267_);
v___x_2269_ = lean_array_get_size(v___x_2268_);
v___x_2270_ = lean_nat_dec_eq(v___x_2269_, v_total_2263_);
if (v___x_2270_ == 0)
{
lean_object* v___f_2271_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___y_2280_; uint8_t v___x_2282_; 
v___f_2271_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__12));
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_sub(v___x_2269_, v___x_2277_);
v___x_2282_ = lean_nat_dec_le(v_total_2263_, v___x_2278_);
if (v___x_2282_ == 0)
{
lean_inc(v___x_2278_);
v___y_2280_ = v___x_2278_;
goto v___jp_2279_;
}
else
{
v___y_2280_ = v_total_2263_;
goto v___jp_2279_;
}
v___jp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2271_, v___x_2269_, v___x_2268_, v___y_2273_, v___y_2274_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2274_);
v___x_2276_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(v_single_2258_, v_multi_2259_, v___x_2275_, v_total_2263_, v_init_2257_);
lean_dec_ref(v___x_2275_);
return v___x_2276_;
}
v___jp_2279_:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_nat_dec_le(v___y_2280_, v___x_2278_);
if (v___x_2281_ == 0)
{
lean_dec(v___x_2278_);
lean_inc(v___y_2280_);
v___y_2273_ = v___y_2280_;
v___y_2274_ = v___y_2280_;
goto v___jp_2272_;
}
else
{
v___y_2273_ = v___y_2280_;
v___y_2274_ = v___x_2278_;
goto v___jp_2272_;
}
}
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(v_single_2258_, v_multi_2259_, v___x_2268_, v_total_2263_, v_init_2257_);
lean_dec(v___x_2268_);
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups(lean_object* v_00_u03b1_2284_, lean_object* v_00_u03c3_2285_, lean_object* v_cands_2286_, lean_object* v_init_2287_, lean_object* v_single_2288_, lean_object* v_multi_2289_){
_start:
{
lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___f_2292_; lean_object* v_total_2293_; size_t v_sz_2294_; size_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___f_2290_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__0));
v___x_2291_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__10));
v___f_2292_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__11));
v_total_2293_ = lean_unsigned_to_nat(0u);
v_sz_2294_ = lean_array_size(v_cands_2286_);
v___x_2295_ = ((size_t)0ULL);
lean_inc_ref(v_cands_2286_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2291_, v_cands_2286_, v___f_2290_, v_sz_2294_, v___x_2295_, v_total_2293_);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
lean_dec(v___x_2296_);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2291_, v_cands_2286_, v___f_2292_, v_sz_2294_, v___x_2295_, v___x_2297_);
v___x_2299_ = lean_array_get_size(v___x_2298_);
v___x_2300_ = lean_nat_dec_eq(v___x_2299_, v_total_2293_);
if (v___x_2300_ == 0)
{
lean_object* v___f_2301_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___y_2310_; uint8_t v___x_2312_; 
v___f_2301_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___closed__12));
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_nat_sub(v___x_2299_, v___x_2307_);
v___x_2312_ = lean_nat_dec_le(v_total_2293_, v___x_2308_);
if (v___x_2312_ == 0)
{
lean_inc(v___x_2308_);
v___y_2310_ = v___x_2308_;
goto v___jp_2309_;
}
else
{
v___y_2310_ = v_total_2293_;
goto v___jp_2309_;
}
v___jp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2301_, v___x_2299_, v___x_2298_, v___y_2303_, v___y_2304_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2304_);
v___x_2306_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(v_single_2288_, v_multi_2289_, v___x_2305_, v_total_2293_, v_init_2287_);
lean_dec_ref(v___x_2305_);
return v___x_2306_;
}
v___jp_2309_:
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_nat_dec_le(v___y_2310_, v___x_2308_);
if (v___x_2311_ == 0)
{
lean_dec(v___x_2308_);
lean_inc(v___y_2310_);
v___y_2303_ = v___y_2310_;
v___y_2304_ = v___y_2310_;
goto v___jp_2302_;
}
else
{
v___y_2303_ = v___y_2310_;
v___y_2304_ = v___x_2308_;
goto v___jp_2302_;
}
}
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___redArg(v_single_2288_, v_multi_2289_, v___x_2298_, v_total_2293_, v_init_2287_);
lean_dec(v___x_2298_);
return v___x_2313_;
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg(lean_object* v_covered_2316_, lean_object* v_as_2317_, size_t v_sz_2318_, size_t v_i_2319_, uint64_t v_b_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = lean_usize_dec_lt(v_i_2319_, v_sz_2318_);
if (v___x_2321_ == 0)
{
return v_b_2320_;
}
else
{
lean_object* v_a_2322_; lean_object* v_fst_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint64_t v___x_2326_; uint64_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; 
v_a_2322_ = lean_array_uget_borrowed(v_as_2317_, v_i_2319_);
v_fst_2323_ = lean_ctor_get(v_a_2322_, 0);
v___x_2324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg___boxed__const__1));
v___x_2325_ = lean_array_get_borrowed(v___x_2324_, v_covered_2316_, v_fst_2323_);
v___x_2326_ = lean_unbox_uint64(v___x_2325_);
v___x_2327_ = lean_uint64_land(v_b_2320_, v___x_2326_);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2319_, v___x_2328_);
v_i_2319_ = v___x_2329_;
v_b_2320_ = v___x_2327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg___boxed(lean_object* v_covered_2331_, lean_object* v_as_2332_, lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_b_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; uint64_t v_b_boxed_2338_; uint64_t v_res_2339_; lean_object* v_r_2340_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_b_boxed_2338_ = lean_unbox_uint64(v_b_2335_);
lean_dec_ref(v_b_2335_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg(v_covered_2331_, v_as_2332_, v_sz_boxed_2336_, v_i_boxed_2337_, v_b_boxed_2338_);
lean_dec_ref(v_as_2332_);
lean_dec_ref(v_covered_2331_);
v_r_2340_ = lean_box_uint64(v_res_2339_);
return v_r_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg(lean_object* v_p_2341_, lean_object* v_as_2342_, size_t v_sz_2343_, size_t v_i_2344_, lean_object* v_b_2345_){
_start:
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_usize_dec_lt(v_i_2344_, v_sz_2343_);
if (v___x_2346_ == 0)
{
return v_b_2345_;
}
else
{
lean_object* v_a_2347_; uint64_t v___y_2349_; lean_object* v___y_2359_; lean_object* v_key_2362_; 
v_a_2347_ = lean_array_uget_borrowed(v_as_2342_, v_i_2344_);
v_key_2362_ = lean_ctor_get(v_a_2347_, 0);
v___y_2359_ = v_key_2362_;
goto v___jp_2358_;
v___jp_2348_:
{
lean_object* v_fst_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; 
v_fst_2350_ = lean_ctor_get(v_p_2341_, 0);
lean_inc(v_a_2347_);
lean_inc(v_fst_2350_);
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_fst_2350_);
lean_ctor_set(v___x_2351_, 1, v_a_2347_);
v___x_2352_ = lean_box_uint64(v___y_2349_);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___x_2351_);
v___x_2354_ = lean_array_push(v_b_2345_, v___x_2353_);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2344_, v___x_2355_);
v_i_2344_ = v___x_2356_;
v_b_2345_ = v___x_2354_;
goto _start;
}
v___jp_2358_:
{
if (lean_obj_tag(v___y_2359_) == 0)
{
uint64_t v___x_2360_; 
v___x_2360_ = 1723ULL;
v___y_2349_ = v___x_2360_;
goto v___jp_2348_;
}
else
{
uint64_t v_hash_2361_; 
v_hash_2361_ = lean_ctor_get_uint64(v___y_2359_, sizeof(void*)*2);
v___y_2349_ = v_hash_2361_;
goto v___jp_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg___boxed(lean_object* v_p_2363_, lean_object* v_as_2364_, lean_object* v_sz_2365_, lean_object* v_i_2366_, lean_object* v_b_2367_){
_start:
{
size_t v_sz_boxed_2368_; size_t v_i_boxed_2369_; lean_object* v_res_2370_; 
v_sz_boxed_2368_ = lean_unbox_usize(v_sz_2365_);
lean_dec(v_sz_2365_);
v_i_boxed_2369_ = lean_unbox_usize(v_i_2366_);
lean_dec(v_i_2366_);
v_res_2370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg(v_p_2363_, v_as_2364_, v_sz_boxed_2368_, v_i_boxed_2369_, v_b_2367_);
lean_dec_ref(v_as_2364_);
lean_dec_ref(v_p_2363_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg(lean_object* v_as_2371_, size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_b_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
if (v___x_2375_ == 0)
{
return v_b_2374_;
}
else
{
lean_object* v_a_2376_; lean_object* v___y_2378_; lean_object* v_snd_2385_; 
v_a_2376_ = lean_array_uget_borrowed(v_as_2371_, v_i_2373_);
v_snd_2385_ = lean_ctor_get(v_a_2376_, 1);
switch(lean_obj_tag(v_snd_2385_))
{
case 0:
{
lean_object* v___x_2386_; 
v___x_2386_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
v___y_2378_ = v___x_2386_;
goto v___jp_2377_;
}
case 1:
{
lean_object* v_children_2387_; 
v_children_2387_ = lean_ctor_get(v_snd_2385_, 1);
v___y_2378_ = v_children_2387_;
goto v___jp_2377_;
}
default: 
{
lean_object* v_children_2388_; 
v_children_2388_ = lean_ctor_get(v_snd_2385_, 2);
v___y_2378_ = v_children_2388_;
goto v___jp_2377_;
}
}
v___jp_2377_:
{
size_t v_sz_2379_; size_t v___x_2380_; lean_object* v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; 
v_sz_2379_ = lean_array_size(v___y_2378_);
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg(v_a_2376_, v___y_2378_, v_sz_2379_, v___x_2380_, v_b_2374_);
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2373_, v___x_2382_);
v_i_2373_ = v___x_2383_;
v_b_2374_ = v___x_2381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg___boxed(lean_object* v_as_2389_, lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_b_2392_){
_start:
{
size_t v_sz_boxed_2393_; size_t v_i_boxed_2394_; lean_object* v_res_2395_; 
v_sz_boxed_2393_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg(v_as_2389_, v_sz_boxed_2393_, v_i_boxed_2394_, v_b_2392_);
lean_dec_ref(v_as_2389_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg(lean_object* v_as_2396_, size_t v_i_2397_, size_t v_stop_2398_, lean_object* v_b_2399_){
_start:
{
lean_object* v___y_2401_; uint8_t v___x_2405_; 
v___x_2405_ = lean_usize_dec_eq(v_i_2397_, v_stop_2398_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v___x_2406_ = lean_array_uget(v_as_2396_, v_i_2397_);
v_fst_2407_ = lean_ctor_get(v___x_2406_, 0);
v_snd_2408_ = lean_ctor_get(v___x_2406_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v___x_2406_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snd_2408_);
lean_inc(v_fst_2407_);
lean_dec(v___x_2406_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_val_2413_; 
if (lean_obj_tag(v_snd_2408_) == 1)
{
lean_dec_ref_known(v_snd_2408_, 2);
lean_del_object(v___x_2410_);
lean_dec(v_fst_2407_);
v___y_2401_ = v_b_2399_;
goto v___jp_2400_;
}
else
{
lean_object* v_val_2418_; 
v_val_2418_ = lean_ctor_get(v_snd_2408_, 1);
lean_inc(v_val_2418_);
lean_dec(v_snd_2408_);
v_val_2413_ = v_val_2418_;
goto v___jp_2412_;
}
v___jp_2412_:
{
lean_object* v___x_2415_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v_fst_2407_);
lean_ctor_set(v___x_2410_, 0, v_val_2413_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_val_2413_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_fst_2407_);
v___x_2415_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_array_push(v_b_2399_, v___x_2415_);
v___y_2401_ = v___x_2416_;
goto v___jp_2400_;
}
}
}
}
else
{
return v_b_2399_;
}
v___jp_2400_:
{
size_t v___x_2402_; size_t v___x_2403_; 
v___x_2402_ = ((size_t)1ULL);
v___x_2403_ = lean_usize_add(v_i_2397_, v___x_2402_);
v_i_2397_ = v___x_2403_;
v_b_2399_ = v___y_2401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg___boxed(lean_object* v_as_2420_, lean_object* v_i_2421_, lean_object* v_stop_2422_, lean_object* v_b_2423_){
_start:
{
size_t v_i_boxed_2424_; size_t v_stop_boxed_2425_; lean_object* v_res_2426_; 
v_i_boxed_2424_ = lean_unbox_usize(v_i_2421_);
lean_dec(v_i_2421_);
v_stop_boxed_2425_ = lean_unbox_usize(v_stop_2422_);
lean_dec(v_stop_2422_);
v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg(v_as_2420_, v_i_boxed_2424_, v_stop_boxed_2425_, v_b_2423_);
lean_dec_ref(v_as_2420_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg(lean_object* v_as_2429_, lean_object* v_start_2430_, lean_object* v_stop_2431_){
_start:
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg___closed__0));
v___x_2433_ = lean_nat_dec_lt(v_start_2430_, v_stop_2431_);
if (v___x_2433_ == 0)
{
return v___x_2432_;
}
else
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = lean_array_get_size(v_as_2429_);
v___x_2435_ = lean_nat_dec_le(v_stop_2431_, v___x_2434_);
if (v___x_2435_ == 0)
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_nat_dec_lt(v_start_2430_, v___x_2434_);
if (v___x_2436_ == 0)
{
return v___x_2432_;
}
else
{
size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_usize_of_nat(v_start_2430_);
v___x_2438_ = lean_usize_of_nat(v___x_2434_);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg(v_as_2429_, v___x_2437_, v___x_2438_, v___x_2432_);
return v___x_2439_;
}
}
else
{
size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = lean_usize_of_nat(v_start_2430_);
v___x_2441_ = lean_usize_of_nat(v_stop_2431_);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg(v_as_2429_, v___x_2440_, v___x_2441_, v___x_2432_);
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg___boxed(lean_object* v_as_2443_, lean_object* v_start_2444_, lean_object* v_stop_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg(v_as_2443_, v_start_2444_, v_stop_2445_);
lean_dec(v_stop_2445_);
lean_dec(v_start_2444_);
lean_dec_ref(v_as_2443_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg(lean_object* v_hi_2447_, lean_object* v_pivot_2448_, lean_object* v_as_2449_, lean_object* v_i_2450_, lean_object* v_k_2451_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_nat_dec_lt(v_k_2451_, v_hi_2447_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec(v_k_2451_);
v___x_2463_ = lean_array_fswap(v_as_2449_, v_i_2450_, v_hi_2447_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_i_2450_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; lean_object* v_snd_2466_; lean_object* v_snd_2467_; lean_object* v_fst_2468_; lean_object* v_fst_2469_; lean_object* v_fst_2470_; lean_object* v_fst_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; uint8_t v___x_2474_; 
v___x_2465_ = lean_array_fget_borrowed(v_as_2449_, v_k_2451_);
v_snd_2466_ = lean_ctor_get(v___x_2465_, 1);
v_snd_2467_ = lean_ctor_get(v_pivot_2448_, 1);
v_fst_2468_ = lean_ctor_get(v___x_2465_, 0);
v_fst_2469_ = lean_ctor_get(v_snd_2466_, 0);
v_fst_2470_ = lean_ctor_get(v_pivot_2448_, 0);
v_fst_2471_ = lean_ctor_get(v_snd_2467_, 0);
v___x_2472_ = lean_unbox_uint64(v_fst_2468_);
v___x_2473_ = lean_unbox_uint64(v_fst_2470_);
v___x_2474_ = lean_uint64_dec_lt(v___x_2472_, v___x_2473_);
if (v___x_2474_ == 0)
{
uint64_t v___x_2475_; uint64_t v___x_2476_; uint8_t v___x_2477_; 
v___x_2475_ = lean_unbox_uint64(v_fst_2468_);
v___x_2476_ = lean_unbox_uint64(v_fst_2470_);
v___x_2477_ = lean_uint64_dec_eq(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
goto v___jp_2458_;
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_lt(v_fst_2469_, v_fst_2471_);
if (v___x_2478_ == 0)
{
goto v___jp_2458_;
}
else
{
goto v___jp_2452_;
}
}
}
else
{
goto v___jp_2452_;
}
}
v___jp_2452_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2453_ = lean_array_fswap(v_as_2449_, v_i_2450_, v_k_2451_);
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_nat_add(v_i_2450_, v___x_2454_);
lean_dec(v_i_2450_);
v___x_2456_ = lean_nat_add(v_k_2451_, v___x_2454_);
lean_dec(v_k_2451_);
v_as_2449_ = v___x_2453_;
v_i_2450_ = v___x_2455_;
v_k_2451_ = v___x_2456_;
goto _start;
}
v___jp_2458_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = lean_nat_add(v_k_2451_, v___x_2459_);
lean_dec(v_k_2451_);
v_k_2451_ = v___x_2460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg___boxed(lean_object* v_hi_2479_, lean_object* v_pivot_2480_, lean_object* v_as_2481_, lean_object* v_i_2482_, lean_object* v_k_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg(v_hi_2479_, v_pivot_2480_, v_as_2481_, v_i_2482_, v_k_2483_);
lean_dec_ref(v_pivot_2480_);
lean_dec(v_hi_2479_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(lean_object* v_n_2485_, lean_object* v_as_2486_, lean_object* v_lo_2487_, lean_object* v_hi_2488_){
_start:
{
lean_object* v___y_2490_; uint8_t v___x_2500_; 
v___x_2500_ = lean_nat_dec_lt(v_lo_2487_, v_hi_2488_);
if (v___x_2500_ == 0)
{
lean_dec(v_lo_2487_);
return v_as_2486_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_mid_2503_; lean_object* v___y_2505_; lean_object* v___y_2511_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2501_ = lean_nat_add(v_lo_2487_, v_hi_2488_);
v___x_2502_ = lean_unsigned_to_nat(1u);
v_mid_2503_ = lean_nat_shiftr(v___x_2501_, v___x_2502_);
lean_dec(v___x_2501_);
v___x_2516_ = lean_array_fget_borrowed(v_as_2486_, v_mid_2503_);
v___x_2517_ = lean_array_fget_borrowed(v_as_2486_, v_lo_2487_);
v___x_2518_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
v___y_2511_ = v_as_2486_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_array_fswap(v_as_2486_, v_lo_2487_, v_mid_2503_);
v___y_2511_ = v___x_2519_;
goto v___jp_2510_;
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2506_ = lean_array_fget_borrowed(v___y_2505_, v_mid_2503_);
v___x_2507_ = lean_array_fget_borrowed(v___y_2505_, v_hi_2488_);
v___x_2508_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3(v___x_2506_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_dec(v_mid_2503_);
v___y_2490_ = v___y_2505_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_array_fswap(v___y_2505_, v_mid_2503_, v_hi_2488_);
lean_dec(v_mid_2503_);
v___y_2490_ = v___x_2509_;
goto v___jp_2489_;
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2512_ = lean_array_fget_borrowed(v___y_2511_, v_hi_2488_);
v___x_2513_ = lean_array_fget_borrowed(v___y_2511_, v_lo_2487_);
v___x_2514_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups___redArg___lam__3(v___x_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
v___y_2505_ = v___y_2511_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_array_fswap(v___y_2511_, v_lo_2487_, v_hi_2488_);
v___y_2505_ = v___x_2515_;
goto v___jp_2504_;
}
}
}
v___jp_2489_:
{
lean_object* v_pivot_2491_; lean_object* v___x_2492_; lean_object* v_fst_2493_; lean_object* v_snd_2494_; uint8_t v___x_2495_; 
v_pivot_2491_ = lean_array_fget(v___y_2490_, v_hi_2488_);
lean_inc_n(v_lo_2487_, 2);
v___x_2492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg(v_hi_2488_, v_pivot_2491_, v___y_2490_, v_lo_2487_, v_lo_2487_);
lean_dec(v_pivot_2491_);
v_fst_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_fst_2493_);
v_snd_2494_ = lean_ctor_get(v___x_2492_, 1);
lean_inc(v_snd_2494_);
lean_dec_ref(v___x_2492_);
v___x_2495_ = lean_nat_dec_le(v_hi_2488_, v_fst_2493_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(v_n_2485_, v_snd_2494_, v_lo_2487_, v_fst_2493_);
v___x_2497_ = lean_unsigned_to_nat(1u);
v___x_2498_ = lean_nat_add(v_fst_2493_, v___x_2497_);
lean_dec(v_fst_2493_);
v_as_2486_ = v___x_2496_;
v_lo_2487_ = v___x_2498_;
goto _start;
}
else
{
lean_dec(v_fst_2493_);
lean_dec(v_lo_2487_);
return v_snd_2494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg___boxed(lean_object* v_n_2520_, lean_object* v_as_2521_, lean_object* v_lo_2522_, lean_object* v_hi_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(v_n_2520_, v_as_2521_, v_lo_2522_, v_hi_2523_);
lean_dec(v_hi_2523_);
lean_dec(v_n_2520_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg(lean_object* v_as_2525_, size_t v_sz_2526_, size_t v_i_2527_, lean_object* v_b_2528_){
_start:
{
lean_object* v___y_2530_; uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_lt(v_i_2527_, v_sz_2526_);
if (v___x_2536_ == 0)
{
return v_b_2528_;
}
else
{
lean_object* v_a_2537_; lean_object* v_snd_2538_; 
v_a_2537_ = lean_array_uget_borrowed(v_as_2525_, v_i_2527_);
v_snd_2538_ = lean_ctor_get(v_a_2537_, 1);
switch(lean_obj_tag(v_snd_2538_))
{
case 0:
{
lean_object* v___x_2539_; 
v___x_2539_ = ((lean_object*)(l_Lean_instInhabitedConstTrie___redArg___closed__0));
v___y_2530_ = v___x_2539_;
goto v___jp_2529_;
}
case 1:
{
lean_object* v_children_2540_; 
v_children_2540_ = lean_ctor_get(v_snd_2538_, 1);
v___y_2530_ = v_children_2540_;
goto v___jp_2529_;
}
default: 
{
lean_object* v_children_2541_; 
v_children_2541_ = lean_ctor_get(v_snd_2538_, 2);
v___y_2530_ = v_children_2541_;
goto v___jp_2529_;
}
}
}
v___jp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; 
v___x_2531_ = lean_array_get_size(v___y_2530_);
v___x_2532_ = lean_nat_add(v_b_2528_, v___x_2531_);
lean_dec(v_b_2528_);
v___x_2533_ = ((size_t)1ULL);
v___x_2534_ = lean_usize_add(v_i_2527_, v___x_2533_);
v_i_2527_ = v___x_2534_;
v_b_2528_ = v___x_2532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg___boxed(lean_object* v_as_2542_, lean_object* v_sz_2543_, lean_object* v_i_2544_, lean_object* v_b_2545_){
_start:
{
size_t v_sz_boxed_2546_; size_t v_i_boxed_2547_; lean_object* v_res_2548_; 
v_sz_boxed_2546_ = lean_unbox_usize(v_sz_2543_);
lean_dec(v_sz_2543_);
v_i_boxed_2547_ = lean_unbox_usize(v_i_2544_);
lean_dec(v_i_2544_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg(v_as_2542_, v_sz_boxed_2546_, v_i_boxed_2547_, v_b_2545_);
lean_dec_ref(v_as_2542_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg(lean_object* v_covered_2549_, lean_object* v_cands_2550_, lean_object* v_sorted_2551_, lean_object* v_idx_2552_, lean_object* v_s_2553_){
_start:
{
lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = lean_array_get_size(v_sorted_2551_);
v___x_2555_ = lean_nat_dec_lt(v_idx_2552_, v___x_2554_);
if (v___x_2555_ == 0)
{
lean_dec(v_idx_2552_);
return v_s_2553_;
}
else
{
lean_object* v___x_2556_; lean_object* v_snd_2557_; lean_object* v_fst_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; lean_object* v_idx_2562_; uint8_t v___x_2563_; 
v___x_2556_ = lean_array_fget_borrowed(v_sorted_2551_, v_idx_2552_);
v_snd_2557_ = lean_ctor_get(v___x_2556_, 1);
v_fst_2558_ = lean_ctor_get(v___x_2556_, 0);
v_fst_2559_ = lean_ctor_get(v_snd_2557_, 0);
v_snd_2560_ = lean_ctor_get(v_snd_2557_, 1);
v___x_2561_ = lean_unsigned_to_nat(1u);
v_idx_2562_ = lean_nat_add(v_idx_2552_, v___x_2561_);
lean_dec(v_idx_2552_);
v___x_2563_ = lean_nat_dec_lt(v_idx_2562_, v___x_2554_);
if (v___x_2563_ == 0)
{
v_idx_2552_ = v_idx_2562_;
goto _start;
}
else
{
lean_object* v___x_2565_; lean_object* v_fst_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2587_; 
v___x_2565_ = lean_array_fget(v_sorted_2551_, v_idx_2562_);
v_fst_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2565_, 1);
lean_dec(v_unused_2588_);
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2587_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_fst_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2587_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint64_t v___x_2570_; uint64_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_unbox_uint64(v_fst_2566_);
lean_dec(v_fst_2566_);
v___x_2571_ = lean_unbox_uint64(v_fst_2558_);
v___x_2572_ = lean_uint64_dec_eq(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_del_object(v___x_2568_);
v_idx_2552_ = v_idx_2562_;
goto _start;
}
else
{
lean_object* v___x_2575_; 
lean_inc(v_snd_2560_);
lean_inc(v_fst_2559_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v_snd_2560_);
lean_ctor_set(v___x_2568_, 0, v_fst_2559_);
v___x_2575_ = v___x_2568_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_fst_2559_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_snd_2560_);
v___x_2575_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint64_t v___x_2579_; lean_object* v_val_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2576_ = lean_mk_empty_array_with_capacity(v___x_2561_);
lean_inc_ref(v___x_2576_);
v___x_2577_ = lean_array_push(v___x_2576_, v___x_2575_);
v___x_2578_ = lean_array_push(v___x_2576_, v___x_2577_);
v___x_2579_ = lean_unbox_uint64(v_fst_2558_);
v_val_2580_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(v_sorted_2551_, v___x_2579_, v_idx_2562_, v___x_2578_);
v_fst_2581_ = lean_ctor_get(v_val_2580_, 0);
lean_inc(v_fst_2581_);
v_snd_2582_ = lean_ctor_get(v_val_2580_, 1);
lean_inc(v_snd_2582_);
lean_dec_ref(v_val_2580_);
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg(v_covered_2549_, v_fst_2581_, v___x_2583_, v_s_2553_);
lean_dec(v_fst_2581_);
v_idx_2552_ = v_snd_2582_;
v_s_2553_ = v___x_2584_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg(lean_object* v_covered_2589_, lean_object* v_key_2590_, lean_object* v_cands_2591_, lean_object* v_acc_2592_){
_start:
{
lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2611_; lean_object* v_acc_2612_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2633_ = lean_array_get_size(v_covered_2589_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_nat_dec_eq(v___x_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
uint64_t v_common_2636_; size_t v_sz_2637_; size_t v___x_2638_; uint64_t v___x_2639_; uint64_t v___x_2640_; uint8_t v___x_2641_; 
v_common_2636_ = 18446744073709551615ULL;
v_sz_2637_ = lean_array_size(v_cands_2591_);
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg(v_covered_2589_, v_cands_2591_, v_sz_2637_, v___x_2638_, v_common_2636_);
v___x_2640_ = 0ULL;
v___x_2641_ = lean_uint64_dec_eq(v___x_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_dec(v_key_2590_);
return v_acc_2592_;
}
else
{
goto v___jp_2624_;
}
}
else
{
goto v___jp_2624_;
}
v___jp_2593_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(v___y_2597_, v___y_2596_, v___y_2595_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec(v___y_2597_);
v___x_2601_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg(v_covered_2589_, v_cands_2591_, v___x_2600_, v___y_2594_, v___y_2598_);
lean_dec_ref(v___x_2600_);
return v___x_2601_;
}
v___jp_2602_:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_nat_dec_le(v___y_2608_, v___y_2605_);
if (v___x_2609_ == 0)
{
lean_dec(v___y_2605_);
lean_inc(v___y_2608_);
v___y_2594_ = v___y_2604_;
v___y_2595_ = v___y_2608_;
v___y_2596_ = v___y_2603_;
v___y_2597_ = v___y_2606_;
v___y_2598_ = v___y_2607_;
v___y_2599_ = v___y_2608_;
goto v___jp_2593_;
}
else
{
v___y_2594_ = v___y_2604_;
v___y_2595_ = v___y_2608_;
v___y_2596_ = v___y_2603_;
v___y_2597_ = v___y_2606_;
v___y_2598_ = v___y_2607_;
v___y_2599_ = v___y_2605_;
goto v___jp_2593_;
}
}
v___jp_2610_:
{
size_t v_sz_2613_; size_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v_sz_2613_ = lean_array_size(v_cands_2591_);
v___x_2614_ = ((size_t)0ULL);
lean_inc(v___y_2611_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg(v_cands_2591_, v_sz_2613_, v___x_2614_, v___y_2611_);
v___x_2616_ = lean_mk_empty_array_with_capacity(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg(v_cands_2591_, v_sz_2613_, v___x_2614_, v___x_2616_);
v___x_2618_ = lean_array_get_size(v___x_2617_);
v___x_2619_ = lean_nat_dec_eq(v___x_2618_, v___y_2611_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = lean_nat_sub(v___x_2618_, v___x_2620_);
v___x_2622_ = lean_nat_dec_le(v___y_2611_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_inc(v___x_2621_);
v___y_2603_ = v___x_2617_;
v___y_2604_ = v___y_2611_;
v___y_2605_ = v___x_2621_;
v___y_2606_ = v___x_2618_;
v___y_2607_ = v_acc_2612_;
v___y_2608_ = v___x_2621_;
goto v___jp_2602_;
}
else
{
lean_inc(v___y_2611_);
v___y_2603_ = v___x_2617_;
v___y_2604_ = v___y_2611_;
v___y_2605_ = v___x_2621_;
v___y_2606_ = v___x_2618_;
v___y_2607_ = v_acc_2612_;
v___y_2608_ = v___y_2611_;
goto v___jp_2602_;
}
}
else
{
lean_object* v___x_2623_; 
v___x_2623_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg(v_covered_2589_, v_cands_2591_, v___x_2617_, v___y_2611_, v_acc_2612_);
lean_dec_ref(v___x_2617_);
return v___x_2623_;
}
}
v___jp_2624_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_entries_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_array_get_size(v_cands_2591_);
v_entries_2627_ = l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg(v_cands_2591_, v___x_2625_, v___x_2626_);
v___x_2628_ = lean_unsigned_to_nat(1u);
v___x_2629_ = lean_array_get_size(v_entries_2627_);
v___x_2630_ = lean_nat_dec_lt(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_dec_ref(v_entries_2627_);
lean_dec(v_key_2590_);
v___y_2611_ = v___x_2625_;
v_acc_2612_ = v_acc_2592_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2631_; lean_object* v_acc_2632_; 
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_key_2590_);
lean_ctor_set(v___x_2631_, 1, v_entries_2627_);
v_acc_2632_ = lean_array_push(v_acc_2592_, v___x_2631_);
v___y_2611_ = v___x_2625_;
v_acc_2612_ = v_acc_2632_;
goto v___jp_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg(lean_object* v_covered_2642_, lean_object* v_groups_2643_, lean_object* v_k_2644_, lean_object* v_s_2645_){
_start:
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = lean_array_get_size(v_groups_2643_);
v___x_2647_ = lean_nat_dec_lt(v_k_2644_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_dec(v_k_2644_);
return v_s_2645_;
}
else
{
lean_object* v_g_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_g_2648_ = lean_array_fget_borrowed(v_groups_2643_, v_k_2644_);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_k_2644_, v___x_2649_);
lean_dec(v_k_2644_);
v___x_2651_ = lean_array_get_size(v_g_2648_);
v___x_2652_ = lean_nat_dec_eq(v___x_2651_, v___x_2649_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_snd_2656_; lean_object* v_key_2657_; lean_object* v___x_2658_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_obj_once(&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0, &l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0_once, _init_l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0);
v___x_2655_ = lean_array_get_borrowed(v___x_2654_, v_g_2648_, v___x_2653_);
v_snd_2656_ = lean_ctor_get(v___x_2655_, 1);
v_key_2657_ = lean_ctor_get(v_snd_2656_, 0);
lean_inc(v_key_2657_);
v___x_2658_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg(v_covered_2642_, v_key_2657_, v_g_2648_, v_s_2645_);
v_k_2644_ = v___x_2650_;
v_s_2645_ = v___x_2658_;
goto _start;
}
else
{
v_k_2644_ = v___x_2650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg___boxed(lean_object* v_covered_2661_, lean_object* v_groups_2662_, lean_object* v_k_2663_, lean_object* v_s_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg(v_covered_2661_, v_groups_2662_, v_k_2663_, v_s_2664_);
lean_dec_ref(v_groups_2662_);
lean_dec_ref(v_covered_2661_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg___boxed(lean_object* v_covered_2666_, lean_object* v_cands_2667_, lean_object* v_sorted_2668_, lean_object* v_idx_2669_, lean_object* v_s_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg(v_covered_2666_, v_cands_2667_, v_sorted_2668_, v_idx_2669_, v_s_2670_);
lean_dec_ref(v_sorted_2668_);
lean_dec_ref(v_cands_2667_);
lean_dec_ref(v_covered_2666_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg___boxed(lean_object* v_covered_2672_, lean_object* v_key_2673_, lean_object* v_cands_2674_, lean_object* v_acc_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg(v_covered_2672_, v_key_2673_, v_cands_2674_, v_acc_2675_);
lean_dec_ref(v_cands_2674_);
lean_dec_ref(v_covered_2672_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux(lean_object* v_00_u03b1_2677_, lean_object* v_covered_2678_, lean_object* v_key_2679_, lean_object* v_cands_2680_, lean_object* v_acc_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg(v_covered_2678_, v_key_2679_, v_cands_2680_, v_acc_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_covered_2684_, lean_object* v_key_2685_, lean_object* v_cands_2686_, lean_object* v_acc_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux(v_00_u03b1_2683_, v_covered_2684_, v_key_2685_, v_cands_2686_, v_acc_2687_);
lean_dec_ref(v_cands_2686_);
lean_dec_ref(v_covered_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0(lean_object* v_00_u03b1_2689_, lean_object* v_p_2690_, lean_object* v_as_2691_, size_t v_sz_2692_, size_t v_i_2693_, lean_object* v_b_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___redArg(v_p_2690_, v_as_2691_, v_sz_2692_, v_i_2693_, v_b_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0___boxed(lean_object* v_00_u03b1_2696_, lean_object* v_p_2697_, lean_object* v_as_2698_, lean_object* v_sz_2699_, lean_object* v_i_2700_, lean_object* v_b_2701_){
_start:
{
size_t v_sz_boxed_2702_; size_t v_i_boxed_2703_; lean_object* v_res_2704_; 
v_sz_boxed_2702_ = lean_unbox_usize(v_sz_2699_);
lean_dec(v_sz_2699_);
v_i_boxed_2703_ = lean_unbox_usize(v_i_2700_);
lean_dec(v_i_2700_);
v_res_2704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__0(v_00_u03b1_2696_, v_p_2697_, v_as_2698_, v_sz_boxed_2702_, v_i_boxed_2703_, v_b_2701_);
lean_dec_ref(v_as_2698_);
lean_dec_ref(v_p_2697_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1(lean_object* v_00_u03b1_2705_, lean_object* v_as_2706_, size_t v_sz_2707_, size_t v_i_2708_, lean_object* v_b_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg(v_as_2706_, v_sz_2707_, v_i_2708_, v_b_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___boxed(lean_object* v_00_u03b1_2711_, lean_object* v_as_2712_, lean_object* v_sz_2713_, lean_object* v_i_2714_, lean_object* v_b_2715_){
_start:
{
size_t v_sz_boxed_2716_; size_t v_i_boxed_2717_; lean_object* v_res_2718_; 
v_sz_boxed_2716_ = lean_unbox_usize(v_sz_2713_);
lean_dec(v_sz_2713_);
v_i_boxed_2717_ = lean_unbox_usize(v_i_2714_);
lean_dec(v_i_2714_);
v_res_2718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1(v_00_u03b1_2711_, v_as_2712_, v_sz_boxed_2716_, v_i_boxed_2717_, v_b_2715_);
lean_dec_ref(v_as_2712_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2(lean_object* v_00_u03b1_2719_, lean_object* v_as_2720_, size_t v_sz_2721_, size_t v_i_2722_, lean_object* v_b_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg(v_as_2720_, v_sz_2721_, v_i_2722_, v_b_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_as_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_b_2729_){
_start:
{
size_t v_sz_boxed_2730_; size_t v_i_boxed_2731_; lean_object* v_res_2732_; 
v_sz_boxed_2730_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2731_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2(v_00_u03b1_2725_, v_as_2726_, v_sz_boxed_2730_, v_i_boxed_2731_, v_b_2729_);
lean_dec_ref(v_as_2726_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3(lean_object* v_00_u03b1_2733_, lean_object* v_n_2734_, lean_object* v_as_2735_, lean_object* v_lo_2736_, lean_object* v_hi_2737_, lean_object* v_w_2738_, lean_object* v_hlo_2739_, lean_object* v_hhi_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(v_n_2734_, v_as_2735_, v_lo_2736_, v_hi_2737_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_n_2743_, lean_object* v_as_2744_, lean_object* v_lo_2745_, lean_object* v_hi_2746_, lean_object* v_w_2747_, lean_object* v_hlo_2748_, lean_object* v_hhi_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3(v_00_u03b1_2742_, v_n_2743_, v_as_2744_, v_lo_2745_, v_hi_2746_, v_w_2747_, v_hlo_2748_, v_hhi_2749_);
lean_dec(v_hi_2746_);
lean_dec(v_n_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4(lean_object* v_00_u03b1_2751_, lean_object* v_covered_2752_, lean_object* v_cands_2753_, lean_object* v_sorted_2754_, lean_object* v_idx_2755_, lean_object* v_s_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___redArg(v_covered_2752_, v_cands_2753_, v_sorted_2754_, v_idx_2755_, v_s_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4___boxed(lean_object* v_00_u03b1_2758_, lean_object* v_covered_2759_, lean_object* v_cands_2760_, lean_object* v_sorted_2761_, lean_object* v_idx_2762_, lean_object* v_s_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4(v_00_u03b1_2758_, v_covered_2759_, v_cands_2760_, v_sorted_2761_, v_idx_2762_, v_s_2763_);
lean_dec_ref(v_sorted_2761_);
lean_dec_ref(v_cands_2760_);
lean_dec_ref(v_covered_2759_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5(lean_object* v_00_u03b1_2765_, lean_object* v_as_2766_, lean_object* v_start_2767_, lean_object* v_stop_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg(v_as_2766_, v_start_2767_, v_stop_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___boxed(lean_object* v_00_u03b1_2770_, lean_object* v_as_2771_, lean_object* v_start_2772_, lean_object* v_stop_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5(v_00_u03b1_2770_, v_as_2771_, v_start_2772_, v_stop_2773_);
lean_dec(v_stop_2773_);
lean_dec(v_start_2772_);
lean_dec_ref(v_as_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6(lean_object* v_00_u03b1_2775_, lean_object* v_covered_2776_, lean_object* v_as_2777_, size_t v_sz_2778_, size_t v_i_2779_, uint64_t v_b_2780_){
_start:
{
uint64_t v___x_2781_; 
v___x_2781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___redArg(v_covered_2776_, v_as_2777_, v_sz_2778_, v_i_2779_, v_b_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6___boxed(lean_object* v_00_u03b1_2782_, lean_object* v_covered_2783_, lean_object* v_as_2784_, lean_object* v_sz_2785_, lean_object* v_i_2786_, lean_object* v_b_2787_){
_start:
{
size_t v_sz_boxed_2788_; size_t v_i_boxed_2789_; uint64_t v_b_boxed_2790_; uint64_t v_res_2791_; lean_object* v_r_2792_; 
v_sz_boxed_2788_ = lean_unbox_usize(v_sz_2785_);
lean_dec(v_sz_2785_);
v_i_boxed_2789_ = lean_unbox_usize(v_i_2786_);
lean_dec(v_i_2786_);
v_b_boxed_2790_ = lean_unbox_uint64(v_b_2787_);
lean_dec_ref(v_b_2787_);
v_res_2791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__6(v_00_u03b1_2782_, v_covered_2783_, v_as_2784_, v_sz_boxed_2788_, v_i_boxed_2789_, v_b_boxed_2790_);
lean_dec_ref(v_as_2784_);
lean_dec_ref(v_covered_2783_);
v_r_2792_ = lean_box_uint64(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3(lean_object* v_00_u03b1_2793_, lean_object* v_n_2794_, lean_object* v_lo_2795_, lean_object* v_hi_2796_, lean_object* v_hhi_2797_, lean_object* v_pivot_2798_, lean_object* v_as_2799_, lean_object* v_i_2800_, lean_object* v_k_2801_, lean_object* v_ilo_2802_, lean_object* v_ik_2803_, lean_object* v_w_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___redArg(v_hi_2796_, v_pivot_2798_, v_as_2799_, v_i_2800_, v_k_2801_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2806_, lean_object* v_n_2807_, lean_object* v_lo_2808_, lean_object* v_hi_2809_, lean_object* v_hhi_2810_, lean_object* v_pivot_2811_, lean_object* v_as_2812_, lean_object* v_i_2813_, lean_object* v_k_2814_, lean_object* v_ilo_2815_, lean_object* v_ik_2816_, lean_object* v_w_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3_spec__3(v_00_u03b1_2806_, v_n_2807_, v_lo_2808_, v_hi_2809_, v_hhi_2810_, v_pivot_2811_, v_as_2812_, v_i_2813_, v_k_2814_, v_ilo_2815_, v_ik_2816_, v_w_2817_);
lean_dec_ref(v_pivot_2811_);
lean_dec(v_hi_2809_);
lean_dec(v_lo_2808_);
lean_dec(v_n_2807_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5(lean_object* v_00_u03b1_2819_, lean_object* v_covered_2820_, lean_object* v_cands_2821_, lean_object* v_groups_2822_, lean_object* v_hgroups_2823_, lean_object* v_k_2824_, lean_object* v_s_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___redArg(v_covered_2820_, v_groups_2822_, v_k_2824_, v_s_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2827_, lean_object* v_covered_2828_, lean_object* v_cands_2829_, lean_object* v_groups_2830_, lean_object* v_hgroups_2831_, lean_object* v_k_2832_, lean_object* v_s_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__4_spec__5(v_00_u03b1_2827_, v_covered_2828_, v_cands_2829_, v_groups_2830_, v_hgroups_2831_, v_k_2832_, v_s_2833_);
lean_dec_ref(v_groups_2830_);
lean_dec_ref(v_cands_2829_);
lean_dec_ref(v_covered_2828_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7(lean_object* v_00_u03b1_2835_, lean_object* v_as_2836_, size_t v_i_2837_, size_t v_stop_2838_, lean_object* v_b_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___redArg(v_as_2836_, v_i_2837_, v_stop_2838_, v_b_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2841_, lean_object* v_as_2842_, lean_object* v_i_2843_, lean_object* v_stop_2844_, lean_object* v_b_2845_){
_start:
{
size_t v_i_boxed_2846_; size_t v_stop_boxed_2847_; lean_object* v_res_2848_; 
v_i_boxed_2846_ = lean_unbox_usize(v_i_2843_);
lean_dec(v_i_2843_);
v_stop_boxed_2847_ = lean_unbox_usize(v_stop_2844_);
lean_dec(v_stop_2844_);
v_res_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5_spec__7(v_00_u03b1_2841_, v_as_2842_, v_i_boxed_2846_, v_stop_boxed_2847_, v_b_2845_);
lean_dec_ref(v_as_2842_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2849_, lean_object* v_h__1_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_apply_2(v_h__1_2850_, v_x_2849_, lean_box(0));
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2852_, lean_object* v_P_2853_, lean_object* v_motive_2854_, lean_object* v_x_2855_, lean_object* v_h__1_2856_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_apply_2(v_h__1_2856_, v_x_2855_, lean_box(0));
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_match__1_splitter___redArg(lean_object* v_x_2858_, lean_object* v_h__1_2859_){
_start:
{
lean_object* v_fst_2860_; lean_object* v_snd_2861_; lean_object* v___x_2862_; 
v_fst_2860_ = lean_ctor_get(v_x_2858_, 0);
lean_inc(v_fst_2860_);
v_snd_2861_ = lean_ctor_get(v_x_2858_, 1);
lean_inc(v_snd_2861_);
lean_dec_ref(v_x_2858_);
v___x_2862_ = lean_apply_2(v_h__1_2859_, v_fst_2860_, v_snd_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_match__1_splitter(lean_object* v_00_u03b1_2863_, lean_object* v_motive_2864_, lean_object* v_x_2865_, lean_object* v_h__1_2866_){
_start:
{
lean_object* v_fst_2867_; lean_object* v_snd_2868_; lean_object* v___x_2869_; 
v_fst_2867_ = lean_ctor_get(v_x_2865_, 0);
lean_inc(v_fst_2867_);
v_snd_2868_ = lean_ctor_get(v_x_2865_, 1);
lean_inc(v_snd_2868_);
lean_dec_ref(v_x_2865_);
v___x_2869_ = lean_apply_2(v_h__1_2866_, v_fst_2867_, v_snd_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates___redArg(lean_object* v_trees_2872_, lean_object* v_covered_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2874_ = lean_array_get_size(v_trees_2872_);
v___x_2875_ = lean_unsigned_to_nat(2u);
v___x_2876_ = lean_nat_dec_lt(v___x_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = ((lean_object*)(l_Lean_ImportedConsts_collectDuplicates___redArg___closed__0));
v___x_2879_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux___redArg(v_covered_2873_, v___x_2877_, v_trees_2872_, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; 
v___x_2880_ = ((lean_object*)(l_Lean_ImportedConsts_collectDuplicates___redArg___closed__0));
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates___redArg___boxed(lean_object* v_trees_2881_, lean_object* v_covered_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_ImportedConsts_collectDuplicates___redArg(v_trees_2881_, v_covered_2882_);
lean_dec_ref(v_covered_2882_);
lean_dec_ref(v_trees_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates(lean_object* v_00_u03b1_2884_, lean_object* v_trees_2885_, lean_object* v_covered_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_ImportedConsts_collectDuplicates___redArg(v_trees_2885_, v_covered_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_collectDuplicates___boxed(lean_object* v_00_u03b1_2888_, lean_object* v_trees_2889_, lean_object* v_covered_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_ImportedConsts_collectDuplicates(v_00_u03b1_2888_, v_trees_2889_, v_covered_2890_);
lean_dec_ref(v_covered_2890_);
lean_dec_ref(v_trees_2889_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg___lam__0(lean_object* v_cs_2892_, lean_object* v_i_2893_, lean_object* v_c_2894_){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v_i_2893_);
lean_ctor_set(v___x_2895_, 1, v_c_2894_);
v___x_2896_ = lean_array_push(v_cs_2892_, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg___lam__0___boxed(lean_object* v_resolve_2897_, lean_object* v_cands_2898_, lean_object* v_x_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg___lam__0(v_resolve_2897_, v_cands_2898_, v_x_2899_);
lean_dec_ref(v_cands_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg(lean_object* v_resolve_2901_, lean_object* v_key_2902_, lean_object* v_cands_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2904_ = lean_array_get_size(v_cands_2903_);
v___x_2905_ = lean_unsigned_to_nat(1u);
v___x_2906_ = lean_nat_dec_eq(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___f_2907_; lean_object* v___y_2909_; lean_object* v___x_2912_; lean_object* v_entries_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
lean_inc_ref(v_cands_2903_);
lean_inc_ref(v_resolve_2901_);
v___f_2907_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2907_, 0, v_resolve_2901_);
lean_closure_set(v___f_2907_, 1, v_cands_2903_);
v___x_2912_ = lean_unsigned_to_nat(0u);
v_entries_2913_ = l_Array_filterMapM___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__5___redArg(v_cands_2903_, v___x_2912_, v___x_2904_);
lean_dec_ref(v_cands_2903_);
v___x_2914_ = lean_array_get_size(v_entries_2913_);
v___x_2915_ = lean_unsigned_to_nat(2u);
v___x_2916_ = lean_nat_dec_lt(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_apply_1(v_resolve_2901_, v_entries_2913_);
v___y_2909_ = v___x_2917_;
goto v___jp_2908_;
}
else
{
uint8_t v___x_2918_; 
lean_dec_ref(v_resolve_2901_);
v___x_2918_ = lean_nat_dec_lt(v___x_2912_, v___x_2914_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_dec_ref(v_entries_2913_);
v___x_2919_ = lean_box(0);
v___y_2909_ = v___x_2919_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_array_fget(v_entries_2913_, v___x_2912_);
lean_dec_ref(v_entries_2913_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
v___y_2909_ = v___x_2921_;
goto v___jp_2908_;
}
}
v___jp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_mk_thunk(v___f_2907_);
v___x_2911_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2911_, 0, v_key_2902_);
lean_ctor_set(v___x_2911_, 1, v___y_2909_);
lean_ctor_set(v___x_2911_, 2, v___x_2910_);
return v___x_2911_;
}
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_fst_2925_; lean_object* v_snd_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_key_2902_);
lean_dec_ref(v_resolve_2901_);
v___x_2922_ = lean_unsigned_to_nat(0u);
v___x_2923_ = lean_obj_once(&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0, &l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0_once, _init_l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0);
v___x_2924_ = lean_array_get(v___x_2923_, v_cands_2903_, v___x_2922_);
lean_dec_ref(v_cands_2903_);
v_fst_2925_ = lean_ctor_get(v___x_2924_, 0);
v_snd_2926_ = lean_ctor_get(v___x_2924_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2924_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_snd_2926_);
lean_inc(v_fst_2925_);
lean_dec(v___x_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_fst_2925_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_snd_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg(lean_object* v_resolve_2934_, lean_object* v_groups_2935_, lean_object* v_k_2936_, lean_object* v_s_2937_){
_start:
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = lean_array_get_size(v_groups_2935_);
v___x_2939_ = lean_nat_dec_lt(v_k_2936_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_dec(v_k_2936_);
lean_dec_ref(v_resolve_2934_);
return v_s_2937_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v_g_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___y_2946_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_obj_once(&l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0, &l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0_once, _init_l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___redArg___closed__0);
v_g_2942_ = lean_array_fget_borrowed(v_groups_2935_, v_k_2936_);
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_nat_add(v_k_2936_, v___x_2943_);
lean_dec(v_k_2936_);
v___x_2950_ = lean_array_get_size(v_g_2942_);
v___x_2951_ = lean_nat_dec_eq(v___x_2950_, v___x_2943_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v_snd_2953_; lean_object* v_key_2954_; 
v___x_2952_ = lean_array_get_borrowed(v___x_2941_, v_g_2942_, v___x_2940_);
v_snd_2953_ = lean_ctor_get(v___x_2952_, 1);
v_key_2954_ = lean_ctor_get(v_snd_2953_, 0);
lean_inc(v_key_2954_);
v___y_2946_ = v_key_2954_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_2955_; lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2966_; 
v___x_2955_ = lean_array_get(v___x_2941_, v_g_2942_, v___x_2940_);
v_fst_2956_ = lean_ctor_get(v___x_2955_, 0);
v_snd_2957_ = lean_ctor_get(v___x_2955_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2959_ = v___x_2955_;
v_isShared_2960_ = v_isSharedCheck_2966_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_snd_2957_);
lean_inc(v_fst_2956_);
lean_dec(v___x_2955_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2966_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_fst_2956_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2957_);
v___x_2962_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_array_push(v_s_2937_, v___x_2962_);
v_k_2936_ = v___x_2944_;
v_s_2937_ = v___x_2963_;
goto _start;
}
}
}
v___jp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_inc(v_g_2942_);
lean_inc_ref(v_resolve_2934_);
v___x_2947_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg(v_resolve_2934_, v___y_2946_, v_g_2942_);
v___x_2948_ = lean_array_push(v_s_2937_, v___x_2947_);
v_k_2936_ = v___x_2944_;
v_s_2937_ = v___x_2948_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg(lean_object* v_resolve_2967_, lean_object* v_cands_2968_, lean_object* v_sorted_2969_, lean_object* v_idx_2970_, lean_object* v_s_2971_){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = lean_array_get_size(v_sorted_2969_);
v___x_2973_ = lean_nat_dec_lt(v_idx_2970_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_dec(v_idx_2970_);
lean_dec_ref(v_resolve_2967_);
return v_s_2971_;
}
else
{
lean_object* v___x_2974_; lean_object* v_snd_2975_; lean_object* v_fst_2976_; lean_object* v_fst_2977_; lean_object* v_snd_2978_; lean_object* v___x_2979_; lean_object* v_idx_2980_; uint8_t v___x_2981_; 
v___x_2974_ = lean_array_fget_borrowed(v_sorted_2969_, v_idx_2970_);
v_snd_2975_ = lean_ctor_get(v___x_2974_, 1);
v_fst_2976_ = lean_ctor_get(v___x_2974_, 0);
v_fst_2977_ = lean_ctor_get(v_snd_2975_, 0);
v_snd_2978_ = lean_ctor_get(v_snd_2975_, 1);
v___x_2979_ = lean_unsigned_to_nat(1u);
v_idx_2980_ = lean_nat_add(v_idx_2970_, v___x_2979_);
lean_dec(v_idx_2970_);
v___x_2981_ = lean_nat_dec_lt(v_idx_2980_, v___x_2972_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_inc(v_snd_2978_);
lean_inc(v_fst_2977_);
v___x_2982_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg___lam__0(v_s_2971_, v_fst_2977_, v_snd_2978_);
v_idx_2970_ = v_idx_2980_;
v_s_2971_ = v___x_2982_;
goto _start;
}
else
{
lean_object* v___x_2984_; lean_object* v_fst_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3007_; 
v___x_2984_ = lean_array_fget(v_sorted_2969_, v_idx_2980_);
v_fst_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v___x_2984_, 1);
lean_dec(v_unused_3008_);
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_3007_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_fst_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3007_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint64_t v___x_2989_; uint64_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2989_ = lean_unbox_uint64(v_fst_2985_);
lean_dec(v_fst_2985_);
v___x_2990_ = lean_unbox_uint64(v_fst_2976_);
v___x_2991_ = lean_uint64_dec_eq(v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_del_object(v___x_2987_);
lean_inc(v_snd_2978_);
lean_inc(v_fst_2977_);
v___x_2992_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg___lam__0(v_s_2971_, v_fst_2977_, v_snd_2978_);
v_idx_2970_ = v_idx_2980_;
v_s_2971_ = v___x_2992_;
goto _start;
}
else
{
lean_object* v___x_2995_; 
lean_inc(v_snd_2978_);
lean_inc(v_fst_2977_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 1, v_snd_2978_);
lean_ctor_set(v___x_2987_, 0, v_fst_2977_);
v___x_2995_ = v___x_2987_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_fst_2977_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_snd_2978_);
v___x_2995_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint64_t v___x_2999_; lean_object* v_val_3000_; lean_object* v_fst_3001_; lean_object* v_snd_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2996_ = lean_mk_empty_array_with_capacity(v___x_2979_);
lean_inc_ref(v___x_2996_);
v___x_2997_ = lean_array_push(v___x_2996_, v___x_2995_);
v___x_2998_ = lean_array_push(v___x_2996_, v___x_2997_);
v___x_2999_ = lean_unbox_uint64(v_fst_2976_);
v_val_3000_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_gather___redArg(v_sorted_2969_, v___x_2999_, v_idx_2980_, v___x_2998_);
v_fst_3001_ = lean_ctor_get(v_val_3000_, 0);
lean_inc(v_fst_3001_);
v_snd_3002_ = lean_ctor_get(v_val_3000_, 1);
lean_inc(v_snd_3002_);
lean_dec_ref(v_val_3000_);
v___x_3003_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_resolve_2967_);
v___x_3004_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg(v_resolve_2967_, v_fst_3001_, v___x_3003_, v_s_2971_);
lean_dec(v_fst_3001_);
v_idx_2970_ = v_snd_3002_;
v_s_2971_ = v___x_3004_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg(lean_object* v_resolve_3009_, lean_object* v_cands_3010_){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; size_t v_sz_3013_; size_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___y_3020_; lean_object* v___y_3021_; uint8_t v___x_3024_; 
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = ((lean_object*)(l_Lean_instInhabitedImportedTree___redArg___closed__0));
v_sz_3013_ = lean_array_size(v_cands_3010_);
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__1___redArg(v_cands_3010_, v_sz_3013_, v___x_3014_, v___x_3011_);
v___x_3016_ = lean_mk_empty_array_with_capacity(v___x_3015_);
lean_dec(v___x_3015_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__2___redArg(v_cands_3010_, v_sz_3013_, v___x_3014_, v___x_3016_);
v___x_3018_ = lean_array_get_size(v___x_3017_);
v___x_3024_ = lean_nat_dec_eq(v___x_3018_, v___x_3011_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___y_3028_; uint8_t v___x_3030_; 
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_sub(v___x_3018_, v___x_3025_);
v___x_3030_ = lean_nat_dec_le(v___x_3011_, v___x_3026_);
if (v___x_3030_ == 0)
{
lean_inc(v___x_3026_);
v___y_3028_ = v___x_3026_;
goto v___jp_3027_;
}
else
{
v___y_3028_ = v___x_3011_;
goto v___jp_3027_;
}
v___jp_3027_:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_nat_dec_le(v___y_3028_, v___x_3026_);
if (v___x_3029_ == 0)
{
lean_dec(v___x_3026_);
lean_inc(v___y_3028_);
v___y_3020_ = v___y_3028_;
v___y_3021_ = v___y_3028_;
goto v___jp_3019_;
}
else
{
v___y_3020_ = v___y_3028_;
v___y_3021_ = v___x_3026_;
goto v___jp_3019_;
}
}
}
else
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg(v_resolve_3009_, v_cands_3010_, v___x_3017_, v___x_3011_, v___x_3012_);
lean_dec_ref(v___x_3017_);
return v___x_3031_;
}
v___jp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_collectDupsAux_spec__3___redArg(v___x_3018_, v___x_3017_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
v___x_3023_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg(v_resolve_3009_, v_cands_3010_, v___x_3022_, v___x_3011_, v___x_3012_);
lean_dec_ref(v___x_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg___lam__0(lean_object* v_resolve_3032_, lean_object* v_cands_3033_, lean_object* v_x_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg(v_resolve_3032_, v_cands_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg___boxed(lean_object* v_resolve_3036_, lean_object* v_cands_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg(v_resolve_3036_, v_cands_3037_);
lean_dec_ref(v_cands_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg___boxed(lean_object* v_resolve_3039_, lean_object* v_groups_3040_, lean_object* v_k_3041_, lean_object* v_s_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg(v_resolve_3039_, v_groups_3040_, v_k_3041_, v_s_3042_);
lean_dec_ref(v_groups_3040_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg___boxed(lean_object* v_resolve_3044_, lean_object* v_cands_3045_, lean_object* v_sorted_3046_, lean_object* v_idx_3047_, lean_object* v_s_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg(v_resolve_3044_, v_cands_3045_, v_sorted_3046_, v_idx_3047_, v_s_3048_);
lean_dec_ref(v_sorted_3046_);
lean_dec_ref(v_cands_3045_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy(lean_object* v_00_u03b1_3050_, lean_object* v_resolve_3051_, lean_object* v_cands_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___redArg(v_resolve_3051_, v_cands_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_resolve_3055_, lean_object* v_cands_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy(v_00_u03b1_3054_, v_resolve_3055_, v_cands_3056_);
lean_dec_ref(v_cands_3056_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy(lean_object* v_00_u03b1_3058_, lean_object* v_resolve_3059_, lean_object* v_key_3060_, lean_object* v_cands_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg(v_resolve_3059_, v_key_3060_, v_cands_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0(lean_object* v_00_u03b1_3063_, lean_object* v_resolve_3064_, lean_object* v_cands_3065_, lean_object* v_sorted_3066_, lean_object* v_idx_3067_, lean_object* v_s_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___redArg(v_resolve_3064_, v_cands_3065_, v_sorted_3066_, v_idx_3067_, v_s_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_resolve_3071_, lean_object* v_cands_3072_, lean_object* v_sorted_3073_, lean_object* v_idx_3074_, lean_object* v_s_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0(v_00_u03b1_3070_, v_resolve_3071_, v_cands_3072_, v_sorted_3073_, v_idx_3074_, v_s_3075_);
lean_dec_ref(v_sorted_3073_);
lean_dec_ref(v_cands_3072_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0(lean_object* v_00_u03b1_3077_, lean_object* v_resolve_3078_, lean_object* v_cands_3079_, lean_object* v_groups_3080_, lean_object* v_hgroups_3081_, lean_object* v_k_3082_, lean_object* v_s_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___redArg(v_resolve_3078_, v_groups_3080_, v_k_3082_, v_s_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_resolve_3086_, lean_object* v_cands_3087_, lean_object* v_groups_3088_, lean_object* v_hgroups_3089_, lean_object* v_k_3090_, lean_object* v_s_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_flush___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_foldChildGroups_go___at___00__private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy_expandLazy_spec__0_spec__0(v_00_u03b1_3085_, v_resolve_3086_, v_cands_3087_, v_groups_3088_, v_hgroups_3089_, v_k_3090_, v_s_3091_);
lean_dec_ref(v_groups_3088_);
lean_dec_ref(v_cands_3087_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_mergeModuleTreesLazy___redArg(lean_object* v_trees_3093_, lean_object* v_resolve_3094_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3095_ = lean_box(0);
v___x_3096_ = lean_box(0);
v___x_3097_ = l___private_Lean_ConstTrie_0__Lean_ImportedConsts_mergeLazy___redArg(v_resolve_3094_, v___x_3096_, v_trees_3093_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3095_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_mergeModuleTreesLazy(lean_object* v_00_u03b1_3099_, lean_object* v_trees_3100_, lean_object* v_resolve_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_ImportedConsts_mergeModuleTreesLazy___redArg(v_trees_3100_, v_resolve_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg(lean_object* v_n_3104_, lean_object* v_f_3105_, lean_object* v_a_3106_){
_start:
{
switch(lean_obj_tag(v_a_3106_))
{
case 0:
{
lean_dec_ref(v_f_3105_);
return v_a_3106_;
}
case 1:
{
lean_object* v_key_3107_; lean_object* v_entry_x3f_3108_; lean_object* v_children_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_key_3107_ = lean_ctor_get(v_a_3106_, 0);
v_entry_x3f_3108_ = lean_ctor_get(v_a_3106_, 1);
v_children_3109_ = lean_ctor_get(v_a_3106_, 2);
v___x_3110_ = lean_obj_once(&l_Lean_instInhabitedImportedTree___closed__0, &l_Lean_instInhabitedImportedTree___closed__0_once, _init_l_Lean_instInhabitedImportedTree___closed__0);
v___x_3111_ = ((lean_object*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg___closed__0));
v___x_3112_ = l___private_Lean_ConstTrie_0__Lean_findChildIdx_x3f___redArg(v___x_3110_, v_children_3109_, v___x_3111_, v_n_3104_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_dec_ref(v_f_3105_);
return v_a_3106_;
}
else
{
lean_object* v_val_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v_val_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = lean_array_get_size(v_children_3109_);
v___x_3115_ = lean_nat_dec_lt(v_val_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_dec(v_val_3113_);
lean_dec_ref(v_f_3105_);
return v_a_3106_;
}
else
{
lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3127_; 
lean_inc_ref(v_children_3109_);
lean_inc(v_entry_x3f_3108_);
lean_inc(v_key_3107_);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; 
v_unused_3128_ = lean_ctor_get(v_a_3106_, 2);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_a_3106_, 1);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_a_3106_, 0);
lean_dec(v_unused_3130_);
v___x_3117_ = v_a_3106_;
v_isShared_3118_ = v_isSharedCheck_3127_;
goto v_resetjp_3116_;
}
else
{
lean_dec(v_a_3106_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3127_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_v_3119_; lean_object* v___x_3120_; lean_object* v_xs_x27_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
v_v_3119_ = lean_array_fget(v_children_3109_, v_val_3113_);
v___x_3120_ = lean_box(0);
v_xs_x27_3121_ = lean_array_fset(v_children_3109_, v_val_3113_, v___x_3120_);
v___x_3122_ = lean_apply_1(v_f_3105_, v_v_3119_);
v___x_3123_ = lean_array_fset(v_xs_x27_3121_, v_val_3113_, v___x_3122_);
lean_dec(v_val_3113_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 2, v___x_3123_);
v___x_3125_ = v___x_3117_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_key_3107_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_entry_x3f_3108_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
default: 
{
lean_object* v_key_3131_; lean_object* v_entry_x3f_3132_; lean_object* v_children_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3142_; 
v_key_3131_ = lean_ctor_get(v_a_3106_, 0);
v_entry_x3f_3132_ = lean_ctor_get(v_a_3106_, 1);
v_children_3133_ = lean_ctor_get(v_a_3106_, 2);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3135_ = v_a_3106_;
v_isShared_3136_ = v_isSharedCheck_3142_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_children_3133_);
lean_inc(v_entry_x3f_3132_);
lean_inc(v_key_3131_);
lean_dec(v_a_3106_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3142_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = lean_thunk_get_own(v_children_3133_);
lean_dec_ref(v_children_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 1);
lean_ctor_set(v___x_3135_, 2, v___x_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_key_3131_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_entry_x3f_3132_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
v_a_3106_ = v___x_3139_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg___boxed(lean_object* v_n_3143_, lean_object* v_f_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg(v_n_3143_, v_f_3144_, v_a_3145_);
lean_dec(v_n_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild(lean_object* v_00_u03b1_3147_, lean_object* v_n_3148_, lean_object* v_f_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___redArg(v_n_3148_, v_f_3149_, v_a_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___boxed(lean_object* v_00_u03b1_3152_, lean_object* v_n_3153_, lean_object* v_f_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild(v_00_u03b1_3152_, v_n_3153_, v_f_3154_, v_a_3155_);
lean_dec(v_n_3153_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt___redArg(lean_object* v_t_3157_, lean_object* v_n_3158_, lean_object* v_f_3159_){
_start:
{
if (lean_obj_tag(v_n_3158_) == 0)
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_apply_1(v_f_3159_, v_t_3157_);
return v___x_3160_;
}
else
{
lean_object* v_pre_3161_; lean_object* v___x_3162_; 
v_pre_3161_ = lean_ctor_get(v_n_3158_, 0);
lean_inc(v_pre_3161_);
v___x_3162_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt_modifyChild___boxed), 4, 3);
lean_closure_set(v___x_3162_, 0, lean_box(0));
lean_closure_set(v___x_3162_, 1, v_n_3158_);
lean_closure_set(v___x_3162_, 2, v_f_3159_);
v_n_3158_ = v_pre_3161_;
v_f_3159_ = v___x_3162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt(lean_object* v_00_u03b1_3164_, lean_object* v_t_3165_, lean_object* v_n_3166_, lean_object* v_f_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt___redArg(v_t_3165_, v_n_3166_, v_f_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__2(lean_object* v___f_3169_, lean_object* v_____x_3170_){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_apply_2(v___f_3169_, v___x_3171_, v_____x_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4(lean_object* v_toApplicative_3173_, lean_object* v_children_3174_, lean_object* v_inst_3175_, lean_object* v___f_3176_, lean_object* v_____r_3177_, lean_object* v_s_3178_){
_start:
{
lean_object* v_toPure_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v_toPure_3179_ = lean_ctor_get(v_toApplicative_3173_, 1);
lean_inc(v_toPure_3179_);
lean_dec_ref(v_toApplicative_3173_);
v___x_3180_ = lean_thunk_get_own(v_children_3174_);
v___x_3181_ = lean_unsigned_to_nat(0u);
v___x_3182_ = lean_array_get_size(v___x_3180_);
v___x_3183_ = lean_nat_dec_lt(v___x_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
lean_dec(v___x_3180_);
lean_dec(v___f_3176_);
lean_dec_ref(v_inst_3175_);
v___x_3184_ = lean_apply_2(v_toPure_3179_, lean_box(0), v_s_3178_);
return v___x_3184_;
}
else
{
size_t v___x_3185_; size_t v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v_toPure_3179_);
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = lean_usize_of_nat(v___x_3182_);
v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3175_, v___f_3176_, v___x_3180_, v___x_3185_, v___x_3186_, v_s_3178_);
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4___boxed(lean_object* v_toApplicative_3188_, lean_object* v_children_3189_, lean_object* v_inst_3190_, lean_object* v___f_3191_, lean_object* v_____r_3192_, lean_object* v_s_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4(v_toApplicative_3188_, v_children_3189_, v_inst_3190_, v___f_3191_, v_____r_3192_, v_s_3193_);
lean_dec_ref(v_children_3189_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__1(lean_object* v_toApplicative_3195_, lean_object* v_children_3196_, lean_object* v_inst_3197_, lean_object* v___f_3198_, lean_object* v_____r_3199_, lean_object* v_s_3200_){
_start:
{
lean_object* v_toPure_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v_toPure_3201_ = lean_ctor_get(v_toApplicative_3195_, 1);
lean_inc(v_toPure_3201_);
lean_dec_ref(v_toApplicative_3195_);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_array_get_size(v_children_3196_);
v___x_3204_ = lean_nat_dec_lt(v___x_3202_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; 
lean_dec(v___f_3198_);
lean_dec_ref(v_inst_3197_);
lean_dec_ref(v_children_3196_);
v___x_3205_ = lean_apply_2(v_toPure_3201_, lean_box(0), v_s_3200_);
return v___x_3205_;
}
else
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v_toPure_3201_);
v___x_3206_ = ((size_t)0ULL);
v___x_3207_ = lean_usize_of_nat(v___x_3203_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3197_, v___f_3198_, v_children_3196_, v___x_3206_, v___x_3207_, v_s_3200_);
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg(lean_object* v_inst_3209_, lean_object* v_t_3210_, lean_object* v_f_3211_, lean_object* v_init_3212_){
_start:
{
switch(lean_obj_tag(v_t_3210_))
{
case 0:
{
lean_object* v_tree_3213_; lean_object* v___x_3214_; 
v_tree_3213_ = lean_ctor_get(v_t_3210_, 1);
lean_inc_ref(v_tree_3213_);
lean_dec_ref_known(v_t_3210_, 2);
v___x_3214_ = l_Lean_ConstTrie_foldlM___redArg(v_inst_3209_, v_tree_3213_, v_f_3211_, v_init_3212_);
return v___x_3214_;
}
case 1:
{
lean_object* v_toApplicative_3215_; lean_object* v_toBind_3216_; lean_object* v_key_3217_; lean_object* v_entry_x3f_3218_; lean_object* v_children_3219_; lean_object* v___f_3220_; lean_object* v___f_3221_; 
v_toApplicative_3215_ = lean_ctor_get(v_inst_3209_, 0);
lean_inc_ref_n(v_toApplicative_3215_, 2);
v_toBind_3216_ = lean_ctor_get(v_inst_3209_, 1);
v_key_3217_ = lean_ctor_get(v_t_3210_, 0);
lean_inc(v_key_3217_);
v_entry_x3f_3218_ = lean_ctor_get(v_t_3210_, 1);
lean_inc(v_entry_x3f_3218_);
v_children_3219_ = lean_ctor_get(v_t_3210_, 2);
lean_inc_ref_n(v_children_3219_, 2);
lean_dec_ref_known(v_t_3210_, 3);
lean_inc(v_f_3211_);
lean_inc_ref_n(v_inst_3209_, 2);
v___f_3220_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_3220_, 0, v_inst_3209_);
lean_closure_set(v___f_3220_, 1, v_f_3211_);
lean_inc_ref(v___f_3220_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__1), 6, 4);
lean_closure_set(v___f_3221_, 0, v_toApplicative_3215_);
lean_closure_set(v___f_3221_, 1, v_children_3219_);
lean_closure_set(v___f_3221_, 2, v_inst_3209_);
lean_closure_set(v___f_3221_, 3, v___f_3220_);
if (lean_obj_tag(v_entry_x3f_3218_) == 1)
{
lean_object* v_val_3222_; lean_object* v_fst_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_inc(v_toBind_3216_);
lean_dec_ref(v___f_3220_);
lean_dec_ref(v_children_3219_);
lean_dec_ref(v_toApplicative_3215_);
lean_dec_ref(v_inst_3209_);
v_val_3222_ = lean_ctor_get(v_entry_x3f_3218_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v_entry_x3f_3218_, 1);
v_fst_3223_ = lean_ctor_get(v_val_3222_, 0);
lean_inc(v_fst_3223_);
lean_dec(v_val_3222_);
v___f_3224_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3224_, 0, v___f_3221_);
v___x_3225_ = lean_apply_3(v_f_3211_, v_init_3212_, v_key_3217_, v_fst_3223_);
v___x_3226_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v___x_3225_, v___f_3224_);
return v___x_3226_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_dec_ref(v___f_3221_);
lean_dec(v_entry_x3f_3218_);
lean_dec(v_key_3217_);
lean_dec(v_f_3211_);
v___x_3227_ = lean_box(0);
v___x_3228_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__1(v_toApplicative_3215_, v_children_3219_, v_inst_3209_, v___f_3220_, v___x_3227_, v_init_3212_);
return v___x_3228_;
}
}
default: 
{
lean_object* v_toApplicative_3229_; lean_object* v_toBind_3230_; lean_object* v_key_3231_; lean_object* v_entry_x3f_3232_; lean_object* v_children_3233_; lean_object* v___f_3234_; lean_object* v___f_3235_; 
v_toApplicative_3229_ = lean_ctor_get(v_inst_3209_, 0);
lean_inc_ref_n(v_toApplicative_3229_, 2);
v_toBind_3230_ = lean_ctor_get(v_inst_3209_, 1);
v_key_3231_ = lean_ctor_get(v_t_3210_, 0);
lean_inc(v_key_3231_);
v_entry_x3f_3232_ = lean_ctor_get(v_t_3210_, 1);
lean_inc(v_entry_x3f_3232_);
v_children_3233_ = lean_ctor_get(v_t_3210_, 2);
lean_inc_ref_n(v_children_3233_, 2);
lean_dec_ref_known(v_t_3210_, 3);
lean_inc(v_f_3211_);
lean_inc_ref_n(v_inst_3209_, 2);
v___f_3234_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_3234_, 0, v_inst_3209_);
lean_closure_set(v___f_3234_, 1, v_f_3211_);
lean_inc_ref(v___f_3234_);
v___f_3235_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3235_, 0, v_toApplicative_3229_);
lean_closure_set(v___f_3235_, 1, v_children_3233_);
lean_closure_set(v___f_3235_, 2, v_inst_3209_);
lean_closure_set(v___f_3235_, 3, v___f_3234_);
if (lean_obj_tag(v_entry_x3f_3232_) == 1)
{
lean_object* v_val_3236_; lean_object* v_fst_3237_; lean_object* v___f_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_inc(v_toBind_3230_);
lean_dec_ref(v___f_3234_);
lean_dec_ref(v_children_3233_);
lean_dec_ref(v_toApplicative_3229_);
lean_dec_ref(v_inst_3209_);
v_val_3236_ = lean_ctor_get(v_entry_x3f_3232_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v_entry_x3f_3232_, 1);
v_fst_3237_ = lean_ctor_get(v_val_3236_, 0);
lean_inc(v_fst_3237_);
lean_dec(v_val_3236_);
v___f_3238_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3238_, 0, v___f_3235_);
v___x_3239_ = lean_apply_3(v_f_3211_, v_init_3212_, v_key_3231_, v_fst_3237_);
v___x_3240_ = lean_apply_4(v_toBind_3230_, lean_box(0), lean_box(0), v___x_3239_, v___f_3238_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_dec_ref(v___f_3235_);
lean_dec(v_entry_x3f_3232_);
lean_dec(v_key_3231_);
lean_dec(v_f_3211_);
v___x_3241_ = lean_box(0);
v___x_3242_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4(v_toApplicative_3229_, v_children_3233_, v_inst_3209_, v___f_3234_, v___x_3241_, v_init_3212_);
lean_dec_ref(v_children_3233_);
return v___x_3242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__0(lean_object* v_inst_3243_, lean_object* v_f_3244_, lean_object* v_s_3245_, lean_object* v_c_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg(v_inst_3243_, v_c_3246_, v_f_3244_, v_s_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM(lean_object* v_m_3248_, lean_object* v_00_u03b1_3249_, lean_object* v_00_u03c3_3250_, lean_object* v_inst_3251_, lean_object* v_t_3252_, lean_object* v_f_3253_, lean_object* v_init_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg(v_inst_3251_, v_t_3252_, v_f_3253_, v_init_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__0(lean_object* v_modIdx_3256_, lean_object* v_f_3257_, lean_object* v_s_3258_, lean_object* v_n_3259_, lean_object* v_v_3260_){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v_v_3260_);
lean_ctor_set(v___x_3261_, 1, v_modIdx_3256_);
v___x_3262_ = lean_apply_3(v_f_3257_, v_s_3258_, v_n_3259_, v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg(lean_object* v_inst_3263_, lean_object* v_t_3264_, lean_object* v_f_3265_, lean_object* v_init_3266_){
_start:
{
switch(lean_obj_tag(v_t_3264_))
{
case 0:
{
lean_object* v_modIdx_3267_; lean_object* v_tree_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; 
v_modIdx_3267_ = lean_ctor_get(v_t_3264_, 0);
lean_inc(v_modIdx_3267_);
v_tree_3268_ = lean_ctor_get(v_t_3264_, 1);
lean_inc_ref(v_tree_3268_);
lean_dec_ref_known(v_t_3264_, 2);
v___f_3269_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_3269_, 0, v_modIdx_3267_);
lean_closure_set(v___f_3269_, 1, v_f_3265_);
v___x_3270_ = l_Lean_ConstTrie_foldlM___redArg(v_inst_3263_, v_tree_3268_, v___f_3269_, v_init_3266_);
return v___x_3270_;
}
case 1:
{
lean_object* v_toApplicative_3271_; lean_object* v_toBind_3272_; lean_object* v_key_3273_; lean_object* v_entry_x3f_3274_; lean_object* v_children_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; 
v_toApplicative_3271_ = lean_ctor_get(v_inst_3263_, 0);
lean_inc_ref_n(v_toApplicative_3271_, 2);
v_toBind_3272_ = lean_ctor_get(v_inst_3263_, 1);
v_key_3273_ = lean_ctor_get(v_t_3264_, 0);
lean_inc(v_key_3273_);
v_entry_x3f_3274_ = lean_ctor_get(v_t_3264_, 1);
lean_inc(v_entry_x3f_3274_);
v_children_3275_ = lean_ctor_get(v_t_3264_, 2);
lean_inc_ref_n(v_children_3275_, 2);
lean_dec_ref_known(v_t_3264_, 3);
lean_inc(v_f_3265_);
lean_inc_ref_n(v_inst_3263_, 2);
v___f_3276_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_3276_, 0, v_inst_3263_);
lean_closure_set(v___f_3276_, 1, v_f_3265_);
lean_inc_ref(v___f_3276_);
v___f_3277_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__1), 6, 4);
lean_closure_set(v___f_3277_, 0, v_toApplicative_3271_);
lean_closure_set(v___f_3277_, 1, v_children_3275_);
lean_closure_set(v___f_3277_, 2, v_inst_3263_);
lean_closure_set(v___f_3277_, 3, v___f_3276_);
if (lean_obj_tag(v_entry_x3f_3274_) == 1)
{
lean_object* v_val_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_inc(v_toBind_3272_);
lean_dec_ref(v___f_3276_);
lean_dec_ref(v_children_3275_);
lean_dec_ref(v_toApplicative_3271_);
lean_dec_ref(v_inst_3263_);
v_val_3278_ = lean_ctor_get(v_entry_x3f_3274_, 0);
lean_inc(v_val_3278_);
lean_dec_ref_known(v_entry_x3f_3274_, 1);
v___f_3279_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3279_, 0, v___f_3277_);
v___x_3280_ = lean_apply_3(v_f_3265_, v_init_3266_, v_key_3273_, v_val_3278_);
v___x_3281_ = lean_apply_4(v_toBind_3272_, lean_box(0), lean_box(0), v___x_3280_, v___f_3279_);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec_ref(v___f_3277_);
lean_dec(v_entry_x3f_3274_);
lean_dec(v_key_3273_);
lean_dec(v_f_3265_);
v___x_3282_ = lean_box(0);
v___x_3283_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__1(v_toApplicative_3271_, v_children_3275_, v_inst_3263_, v___f_3276_, v___x_3282_, v_init_3266_);
return v___x_3283_;
}
}
default: 
{
lean_object* v_toApplicative_3284_; lean_object* v_toBind_3285_; lean_object* v_key_3286_; lean_object* v_entry_x3f_3287_; lean_object* v_children_3288_; lean_object* v___f_3289_; lean_object* v___f_3290_; 
v_toApplicative_3284_ = lean_ctor_get(v_inst_3263_, 0);
lean_inc_ref_n(v_toApplicative_3284_, 2);
v_toBind_3285_ = lean_ctor_get(v_inst_3263_, 1);
v_key_3286_ = lean_ctor_get(v_t_3264_, 0);
lean_inc(v_key_3286_);
v_entry_x3f_3287_ = lean_ctor_get(v_t_3264_, 1);
lean_inc(v_entry_x3f_3287_);
v_children_3288_ = lean_ctor_get(v_t_3264_, 2);
lean_inc_ref_n(v_children_3288_, 2);
lean_dec_ref_known(v_t_3264_, 3);
lean_inc(v_f_3265_);
lean_inc_ref_n(v_inst_3263_, 2);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_3289_, 0, v_inst_3263_);
lean_closure_set(v___f_3289_, 1, v_f_3265_);
lean_inc_ref(v___f_3289_);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3290_, 0, v_toApplicative_3284_);
lean_closure_set(v___f_3290_, 1, v_children_3288_);
lean_closure_set(v___f_3290_, 2, v_inst_3263_);
lean_closure_set(v___f_3290_, 3, v___f_3289_);
if (lean_obj_tag(v_entry_x3f_3287_) == 1)
{
lean_object* v_val_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_inc(v_toBind_3285_);
lean_dec_ref(v___f_3289_);
lean_dec_ref(v_children_3288_);
lean_dec_ref(v_toApplicative_3284_);
lean_dec_ref(v_inst_3263_);
v_val_3291_ = lean_ctor_get(v_entry_x3f_3287_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v_entry_x3f_3287_, 1);
v___f_3292_ = lean_alloc_closure((void*)(l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3292_, 0, v___f_3290_);
v___x_3293_ = lean_apply_3(v_f_3265_, v_init_3266_, v_key_3286_, v_val_3291_);
v___x_3294_ = lean_apply_4(v_toBind_3285_, lean_box(0), lean_box(0), v___x_3293_, v___f_3292_);
return v___x_3294_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec_ref(v___f_3290_);
lean_dec(v_entry_x3f_3287_);
lean_dec(v_key_3286_);
lean_dec(v_f_3265_);
v___x_3295_ = lean_box(0);
v___x_3296_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg___lam__4(v_toApplicative_3284_, v_children_3288_, v_inst_3263_, v___f_3289_, v___x_3295_, v_init_3266_);
lean_dec_ref(v_children_3288_);
return v___x_3296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg___lam__1(lean_object* v_inst_3297_, lean_object* v_f_3298_, lean_object* v_s_3299_, lean_object* v_c_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg(v_inst_3297_, v_c_3300_, v_f_3298_, v_s_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM(lean_object* v_m_3302_, lean_object* v_00_u03b1_3303_, lean_object* v_00_u03c3_3304_, lean_object* v_inst_3305_, lean_object* v_t_3306_, lean_object* v_f_3307_, lean_object* v_init_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg(v_inst_3305_, v_t_3306_, v_f_3307_, v_init_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_modifyAt___redArg(lean_object* v_t_3310_, lean_object* v_n_3311_, lean_object* v_f_3312_){
_start:
{
lean_object* v_tree_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3322_; 
v_tree_3313_ = lean_ctor_get(v_t_3310_, 1);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_t_3310_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; 
v_unused_3323_ = lean_ctor_get(v_t_3310_, 0);
lean_dec(v_unused_3323_);
v___x_3315_ = v_t_3310_;
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_tree_3313_);
lean_dec(v_t_3310_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3317_ = lean_box(0);
v___x_3318_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_modifyAt___redArg(v_tree_3313_, v_n_3311_, v_f_3312_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v___x_3318_);
lean_ctor_set(v___x_3315_, 0, v___x_3317_);
v___x_3320_ = v___x_3315_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_modifyAt(lean_object* v_00_u03b1_3324_, lean_object* v_t_3325_, lean_object* v_n_3326_, lean_object* v_f_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_ImportedConsts_modifyAt___redArg(v_t_3325_, v_n_3326_, v_f_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___redArg(lean_object* v_inst_3329_, lean_object* v_t_3330_, lean_object* v_f_3331_, lean_object* v_init_3332_){
_start:
{
lean_object* v_tree_3333_; lean_object* v___x_3334_; 
v_tree_3333_ = lean_ctor_get(v_t_3330_, 1);
lean_inc_ref(v_tree_3333_);
lean_dec_ref(v_t_3330_);
v___x_3334_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___redArg(v_inst_3329_, v_tree_3333_, v_f_3331_, v_init_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM(lean_object* v_m_3335_, lean_object* v_00_u03b1_3336_, lean_object* v_00_u03c3_3337_, lean_object* v_inst_3338_, lean_object* v_t_3339_, lean_object* v_f_3340_, lean_object* v_init_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_ImportedConsts_foldlM___redArg(v_inst_3338_, v_t_3339_, v_f_3340_, v_init_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___redArg(lean_object* v_t_3343_, lean_object* v_f_3344_, lean_object* v_init_3345_){
_start:
{
switch(lean_obj_tag(v_t_3343_))
{
case 0:
{
lean_object* v_key_3346_; lean_object* v_val_3347_; lean_object* v___x_3348_; 
v_key_3346_ = lean_ctor_get(v_t_3343_, 0);
lean_inc(v_key_3346_);
v_val_3347_ = lean_ctor_get(v_t_3343_, 1);
lean_inc(v_val_3347_);
lean_dec_ref_known(v_t_3343_, 2);
v___x_3348_ = lean_apply_3(v_f_3344_, v_init_3345_, v_key_3346_, v_val_3347_);
return v___x_3348_;
}
case 1:
{
lean_object* v_children_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_children_3349_ = lean_ctor_get(v_t_3343_, 1);
lean_inc_ref(v_children_3349_);
lean_dec_ref_known(v_t_3343_, 2);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_array_get_size(v_children_3349_);
v___x_3352_ = lean_nat_dec_lt(v___x_3350_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_dec_ref(v_children_3349_);
lean_dec(v_f_3344_);
return v_init_3345_;
}
else
{
size_t v___x_3353_; size_t v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = lean_usize_of_nat(v___x_3351_);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3344_, v_children_3349_, v___x_3353_, v___x_3354_, v_init_3345_);
lean_dec_ref(v_children_3349_);
return v___x_3355_;
}
}
default: 
{
lean_object* v_key_3356_; lean_object* v_val_3357_; lean_object* v_children_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_key_3356_ = lean_ctor_get(v_t_3343_, 0);
lean_inc(v_key_3356_);
v_val_3357_ = lean_ctor_get(v_t_3343_, 1);
lean_inc(v_val_3357_);
v_children_3358_ = lean_ctor_get(v_t_3343_, 2);
lean_inc_ref(v_children_3358_);
lean_dec_ref_known(v_t_3343_, 3);
lean_inc(v_f_3344_);
v___x_3359_ = lean_apply_3(v_f_3344_, v_init_3345_, v_key_3356_, v_val_3357_);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = lean_array_get_size(v_children_3358_);
v___x_3362_ = lean_nat_dec_lt(v___x_3360_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_dec_ref(v_children_3358_);
lean_dec(v_f_3344_);
return v___x_3359_;
}
else
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = lean_usize_of_nat(v___x_3361_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3344_, v_children_3358_, v___x_3363_, v___x_3364_, v___x_3359_);
lean_dec_ref(v_children_3358_);
return v___x_3365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3366_, lean_object* v_as_3367_, size_t v_i_3368_, size_t v_stop_3369_, lean_object* v_b_3370_){
_start:
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_usize_dec_eq(v_i_3368_, v_stop_3369_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; size_t v___x_3374_; size_t v___x_3375_; 
v___x_3372_ = lean_array_uget_borrowed(v_as_3367_, v_i_3368_);
lean_inc(v_f_3366_);
lean_inc(v___x_3372_);
v___x_3373_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___redArg(v___x_3372_, v_f_3366_, v_b_3370_);
v___x_3374_ = ((size_t)1ULL);
v___x_3375_ = lean_usize_add(v_i_3368_, v___x_3374_);
v_i_3368_ = v___x_3375_;
v_b_3370_ = v___x_3373_;
goto _start;
}
else
{
lean_dec(v_f_3366_);
return v_b_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3377_, lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_, lean_object* v_b_3381_){
_start:
{
size_t v_i_boxed_3382_; size_t v_stop_boxed_3383_; lean_object* v_res_3384_; 
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3383_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3377_, v_as_3378_, v_i_boxed_3382_, v_stop_boxed_3383_, v_b_3381_);
lean_dec_ref(v_as_3378_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___redArg(lean_object* v_t_3385_, lean_object* v_f_3386_, lean_object* v_init_3387_){
_start:
{
switch(lean_obj_tag(v_t_3385_))
{
case 0:
{
lean_object* v_tree_3388_; lean_object* v___x_3389_; 
v_tree_3388_ = lean_ctor_get(v_t_3385_, 1);
lean_inc_ref(v_tree_3388_);
lean_dec_ref_known(v_t_3385_, 2);
v___x_3389_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___redArg(v_tree_3388_, v_f_3386_, v_init_3387_);
return v___x_3389_;
}
case 1:
{
lean_object* v_key_3390_; lean_object* v_entry_x3f_3391_; lean_object* v_children_3392_; lean_object* v_s_3394_; 
v_key_3390_ = lean_ctor_get(v_t_3385_, 0);
lean_inc(v_key_3390_);
v_entry_x3f_3391_ = lean_ctor_get(v_t_3385_, 1);
lean_inc(v_entry_x3f_3391_);
v_children_3392_ = lean_ctor_get(v_t_3385_, 2);
lean_inc_ref(v_children_3392_);
lean_dec_ref_known(v_t_3385_, 3);
if (lean_obj_tag(v_entry_x3f_3391_) == 1)
{
lean_object* v_val_3401_; lean_object* v_fst_3402_; lean_object* v___x_3403_; 
v_val_3401_ = lean_ctor_get(v_entry_x3f_3391_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v_entry_x3f_3391_, 1);
v_fst_3402_ = lean_ctor_get(v_val_3401_, 0);
lean_inc(v_fst_3402_);
lean_dec(v_val_3401_);
lean_inc(v_f_3386_);
v___x_3403_ = lean_apply_3(v_f_3386_, v_init_3387_, v_key_3390_, v_fst_3402_);
v_s_3394_ = v___x_3403_;
goto v___jp_3393_;
}
else
{
lean_dec(v_entry_x3f_3391_);
lean_dec(v_key_3390_);
v_s_3394_ = v_init_3387_;
goto v___jp_3393_;
}
v___jp_3393_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = lean_array_get_size(v_children_3392_);
v___x_3397_ = lean_nat_dec_lt(v___x_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v_children_3392_);
lean_dec(v_f_3386_);
return v_s_3394_;
}
else
{
size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = ((size_t)0ULL);
v___x_3399_ = lean_usize_of_nat(v___x_3396_);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg(v_f_3386_, v_children_3392_, v___x_3398_, v___x_3399_, v_s_3394_);
lean_dec_ref(v_children_3392_);
return v___x_3400_;
}
}
}
default: 
{
lean_object* v_key_3404_; lean_object* v_entry_x3f_3405_; lean_object* v_children_3406_; lean_object* v_s_3408_; 
v_key_3404_ = lean_ctor_get(v_t_3385_, 0);
lean_inc(v_key_3404_);
v_entry_x3f_3405_ = lean_ctor_get(v_t_3385_, 1);
lean_inc(v_entry_x3f_3405_);
v_children_3406_ = lean_ctor_get(v_t_3385_, 2);
lean_inc_ref(v_children_3406_);
lean_dec_ref_known(v_t_3385_, 3);
if (lean_obj_tag(v_entry_x3f_3405_) == 1)
{
lean_object* v_val_3416_; lean_object* v_fst_3417_; lean_object* v___x_3418_; 
v_val_3416_ = lean_ctor_get(v_entry_x3f_3405_, 0);
lean_inc(v_val_3416_);
lean_dec_ref_known(v_entry_x3f_3405_, 1);
v_fst_3417_ = lean_ctor_get(v_val_3416_, 0);
lean_inc(v_fst_3417_);
lean_dec(v_val_3416_);
lean_inc(v_f_3386_);
v___x_3418_ = lean_apply_3(v_f_3386_, v_init_3387_, v_key_3404_, v_fst_3417_);
v_s_3408_ = v___x_3418_;
goto v___jp_3407_;
}
else
{
lean_dec(v_entry_x3f_3405_);
lean_dec(v_key_3404_);
v_s_3408_ = v_init_3387_;
goto v___jp_3407_;
}
v___jp_3407_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3409_ = lean_thunk_get_own(v_children_3406_);
lean_dec_ref(v_children_3406_);
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = lean_array_get_size(v___x_3409_);
v___x_3412_ = lean_nat_dec_lt(v___x_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_dec(v___x_3409_);
lean_dec(v_f_3386_);
return v_s_3408_;
}
else
{
size_t v___x_3413_; size_t v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = ((size_t)0ULL);
v___x_3414_ = lean_usize_of_nat(v___x_3411_);
v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg(v_f_3386_, v___x_3409_, v___x_3413_, v___x_3414_, v_s_3408_);
lean_dec(v___x_3409_);
return v___x_3415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg(lean_object* v_f_3419_, lean_object* v_as_3420_, size_t v_i_3421_, size_t v_stop_3422_, lean_object* v_b_3423_){
_start:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_usize_dec_eq(v_i_3421_, v_stop_3422_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; size_t v___x_3427_; size_t v___x_3428_; 
v___x_3425_ = lean_array_uget_borrowed(v_as_3420_, v_i_3421_);
lean_inc(v_f_3419_);
lean_inc(v___x_3425_);
v___x_3426_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___redArg(v___x_3425_, v_f_3419_, v_b_3423_);
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3421_, v___x_3427_);
v_i_3421_ = v___x_3428_;
v_b_3423_ = v___x_3426_;
goto _start;
}
else
{
lean_dec(v_f_3419_);
return v_b_3423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_3430_, lean_object* v_as_3431_, lean_object* v_i_3432_, lean_object* v_stop_3433_, lean_object* v_b_3434_){
_start:
{
size_t v_i_boxed_3435_; size_t v_stop_boxed_3436_; lean_object* v_res_3437_; 
v_i_boxed_3435_ = lean_unbox_usize(v_i_3432_);
lean_dec(v_i_3432_);
v_stop_boxed_3436_ = lean_unbox_usize(v_stop_3433_);
lean_dec(v_stop_3433_);
v_res_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg(v_f_3430_, v_as_3431_, v_i_boxed_3435_, v_stop_boxed_3436_, v_b_3434_);
lean_dec_ref(v_as_3431_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(lean_object* v_t_3438_, lean_object* v_f_3439_, lean_object* v_init_3440_){
_start:
{
lean_object* v_tree_3441_; lean_object* v___x_3442_; 
v_tree_3441_ = lean_ctor_get(v_t_3438_, 1);
lean_inc_ref(v_tree_3441_);
lean_dec_ref(v_t_3438_);
v___x_3442_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___redArg(v_tree_3441_, v_f_3439_, v_init_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldl___redArg(lean_object* v_t_3443_, lean_object* v_f_3444_, lean_object* v_init_3445_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(v_t_3443_, v_f_3444_, v_init_3445_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldl(lean_object* v_00_u03b1_3447_, lean_object* v_00_u03c3_3448_, lean_object* v_t_3449_, lean_object* v_f_3450_, lean_object* v_init_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(v_t_3449_, v_f_3450_, v_init_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0(lean_object* v_00_u03b1_3453_, lean_object* v_00_u03c3_3454_, lean_object* v_t_3455_, lean_object* v_f_3456_, lean_object* v_init_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(v_t_3455_, v_f_3456_, v_init_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0(lean_object* v_00_u03b1_3459_, lean_object* v_00_u03c3_3460_, lean_object* v_t_3461_, lean_object* v_f_3462_, lean_object* v_init_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___redArg(v_t_3461_, v_f_3462_, v_init_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3465_, lean_object* v_00_u03c3_3466_, lean_object* v_t_3467_, lean_object* v_f_3468_, lean_object* v_init_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___redArg(v_t_3467_, v_f_3468_, v_init_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3471_, lean_object* v_00_u03c3_3472_, lean_object* v_f_3473_, lean_object* v_as_3474_, size_t v_i_3475_, size_t v_stop_3476_, lean_object* v_b_3477_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___redArg(v_f_3473_, v_as_3474_, v_i_3475_, v_stop_3476_, v_b_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_00_u03c3_3480_, lean_object* v_f_3481_, lean_object* v_as_3482_, lean_object* v_i_3483_, lean_object* v_stop_3484_, lean_object* v_b_3485_){
_start:
{
size_t v_i_boxed_3486_; size_t v_stop_boxed_3487_; lean_object* v_res_3488_; 
v_i_boxed_3486_ = lean_unbox_usize(v_i_3483_);
lean_dec(v_i_3483_);
v_stop_boxed_3487_ = lean_unbox_usize(v_stop_3484_);
lean_dec(v_stop_3484_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2(v_00_u03b1_3479_, v_00_u03c3_3480_, v_f_3481_, v_as_3482_, v_i_boxed_3486_, v_stop_boxed_3487_, v_b_3485_);
lean_dec_ref(v_as_3482_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3489_, lean_object* v_00_u03c3_3490_, lean_object* v_f_3491_, lean_object* v_as_3492_, size_t v_i_3493_, size_t v_stop_3494_, lean_object* v_b_3495_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3491_, v_as_3492_, v_i_3493_, v_stop_3494_, v_b_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3497_, lean_object* v_00_u03c3_3498_, lean_object* v_f_3499_, lean_object* v_as_3500_, lean_object* v_i_3501_, lean_object* v_stop_3502_, lean_object* v_b_3503_){
_start:
{
size_t v_i_boxed_3504_; size_t v_stop_boxed_3505_; lean_object* v_res_3506_; 
v_i_boxed_3504_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_stop_boxed_3505_ = lean_unbox_usize(v_stop_3502_);
lean_dec(v_stop_3502_);
v_res_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3497_, v_00_u03c3_3498_, v_f_3499_, v_as_3500_, v_i_boxed_3504_, v_stop_boxed_3505_, v_b_3503_);
lean_dec_ref(v_as_3500_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlEntriesM___redArg(lean_object* v_inst_3507_, lean_object* v_t_3508_, lean_object* v_f_3509_, lean_object* v_init_3510_){
_start:
{
lean_object* v_tree_3511_; lean_object* v___x_3512_; 
v_tree_3511_ = lean_ctor_get(v_t_3508_, 1);
lean_inc_ref(v_tree_3511_);
lean_dec_ref(v_t_3508_);
v___x_3512_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlEntriesM___redArg(v_inst_3507_, v_tree_3511_, v_f_3509_, v_init_3510_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlEntriesM(lean_object* v_m_3513_, lean_object* v_00_u03b1_3514_, lean_object* v_00_u03c3_3515_, lean_object* v_inst_3516_, lean_object* v_t_3517_, lean_object* v_f_3518_, lean_object* v_init_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_ImportedConsts_foldlEntriesM___redArg(v_inst_3516_, v_t_3517_, v_f_3518_, v_init_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___redArg___lam__0(lean_object* v_f_3521_, lean_object* v_x_3522_, lean_object* v_n_3523_, lean_object* v_v_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_apply_2(v_f_3521_, v_n_3523_, v_v_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___redArg(lean_object* v_inst_3526_, lean_object* v_t_3527_, lean_object* v_f_3528_){
_start:
{
lean_object* v___f_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3529_, 0, v_f_3528_);
v___x_3530_ = lean_box(0);
v___x_3531_ = l_Lean_ImportedConsts_foldlM___redArg(v_inst_3526_, v_t_3527_, v___f_3529_, v___x_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM(lean_object* v_m_3532_, lean_object* v_00_u03b1_3533_, lean_object* v_inst_3534_, lean_object* v_t_3535_, lean_object* v_f_3536_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_ImportedConsts_forM___redArg(v_inst_3534_, v_t_3535_, v_f_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0(lean_object* v_n_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = lean_nat_add(v_n_3538_, v___x_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_n_3543_, lean_object* v_x_3544_, lean_object* v_x_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0(v_n_3543_, v_x_3544_, v_x_3545_);
lean_dec(v_x_3545_);
lean_dec(v_x_3544_);
lean_dec(v_n_3543_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_n_3547_, lean_object* v_x_3548_, lean_object* v_x_3549_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_unsigned_to_nat(1u);
v___x_3551_ = lean_nat_add(v_n_3547_, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_n_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0(v_n_3552_, v_x_3553_, v_x_3554_);
lean_dec(v_x_3554_);
lean_dec(v_x_3553_);
lean_dec(v_n_3552_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg(lean_object* v_t_3556_, lean_object* v_init_3557_){
_start:
{
switch(lean_obj_tag(v_t_3556_))
{
case 0:
{
lean_object* v_key_3558_; lean_object* v_val_3559_; lean_object* v___x_3560_; 
v_key_3558_ = lean_ctor_get(v_t_3556_, 0);
v_val_3559_ = lean_ctor_get(v_t_3556_, 1);
v___x_3560_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0(v_init_3557_, v_key_3558_, v_val_3559_);
lean_dec(v_init_3557_);
return v___x_3560_;
}
case 1:
{
lean_object* v_children_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_children_3561_ = lean_ctor_get(v_t_3556_, 1);
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = lean_array_get_size(v_children_3561_);
v___x_3564_ = lean_nat_dec_lt(v___x_3562_, v___x_3563_);
if (v___x_3564_ == 0)
{
return v_init_3557_;
}
else
{
size_t v___x_3565_; size_t v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = ((size_t)0ULL);
v___x_3566_ = lean_usize_of_nat(v___x_3563_);
v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg(v_children_3561_, v___x_3565_, v___x_3566_, v_init_3557_);
return v___x_3567_;
}
}
default: 
{
lean_object* v_key_3568_; lean_object* v_val_3569_; lean_object* v_children_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v_key_3568_ = lean_ctor_get(v_t_3556_, 0);
v_val_3569_ = lean_ctor_get(v_t_3556_, 1);
v_children_3570_ = lean_ctor_get(v_t_3556_, 2);
v___x_3571_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___lam__0(v_init_3557_, v_key_3568_, v_val_3569_);
lean_dec(v_init_3557_);
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3573_ = lean_array_get_size(v_children_3570_);
v___x_3574_ = lean_nat_dec_lt(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
return v___x_3571_;
}
else
{
size_t v___x_3575_; size_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = ((size_t)0ULL);
v___x_3576_ = lean_usize_of_nat(v___x_3573_);
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg(v_children_3570_, v___x_3575_, v___x_3576_, v___x_3571_);
return v___x_3577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_as_3578_, size_t v_i_3579_, size_t v_stop_3580_, lean_object* v_b_3581_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_eq(v_i_3579_, v_stop_3580_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; size_t v___x_3585_; size_t v___x_3586_; 
v___x_3583_ = lean_array_uget_borrowed(v_as_3578_, v_i_3579_);
v___x_3584_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg(v___x_3583_, v_b_3581_);
v___x_3585_ = ((size_t)1ULL);
v___x_3586_ = lean_usize_add(v_i_3579_, v___x_3585_);
v_i_3579_ = v___x_3586_;
v_b_3581_ = v___x_3584_;
goto _start;
}
else
{
return v_b_3581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_3588_, lean_object* v_i_3589_, lean_object* v_stop_3590_, lean_object* v_b_3591_){
_start:
{
size_t v_i_boxed_3592_; size_t v_stop_boxed_3593_; lean_object* v_res_3594_; 
v_i_boxed_3592_ = lean_unbox_usize(v_i_3589_);
lean_dec(v_i_3589_);
v_stop_boxed_3593_ = lean_unbox_usize(v_stop_3590_);
lean_dec(v_stop_3590_);
v_res_3594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg(v_as_3588_, v_i_boxed_3592_, v_stop_boxed_3593_, v_b_3591_);
lean_dec_ref(v_as_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_3595_, lean_object* v_init_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg(v_t_3595_, v_init_3596_);
lean_dec_ref(v_t_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg(lean_object* v_t_3598_, lean_object* v_init_3599_){
_start:
{
switch(lean_obj_tag(v_t_3598_))
{
case 0:
{
lean_object* v_tree_3600_; lean_object* v___x_3601_; 
v_tree_3600_ = lean_ctor_get(v_t_3598_, 1);
v___x_3601_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg(v_tree_3600_, v_init_3599_);
return v___x_3601_;
}
case 1:
{
lean_object* v_key_3602_; lean_object* v_entry_x3f_3603_; lean_object* v_children_3604_; lean_object* v_s_3606_; 
v_key_3602_ = lean_ctor_get(v_t_3598_, 0);
v_entry_x3f_3603_ = lean_ctor_get(v_t_3598_, 1);
v_children_3604_ = lean_ctor_get(v_t_3598_, 2);
if (lean_obj_tag(v_entry_x3f_3603_) == 1)
{
lean_object* v_val_3613_; lean_object* v_fst_3614_; lean_object* v___x_3615_; 
v_val_3613_ = lean_ctor_get(v_entry_x3f_3603_, 0);
v_fst_3614_ = lean_ctor_get(v_val_3613_, 0);
v___x_3615_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0(v_init_3599_, v_key_3602_, v_fst_3614_);
lean_dec(v_init_3599_);
v_s_3606_ = v___x_3615_;
goto v___jp_3605_;
}
else
{
v_s_3606_ = v_init_3599_;
goto v___jp_3605_;
}
v___jp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = lean_array_get_size(v_children_3604_);
v___x_3609_ = lean_nat_dec_lt(v___x_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
return v_s_3606_;
}
else
{
size_t v___x_3610_; size_t v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = ((size_t)0ULL);
v___x_3611_ = lean_usize_of_nat(v___x_3608_);
v___x_3612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg(v_children_3604_, v___x_3610_, v___x_3611_, v_s_3606_);
return v___x_3612_;
}
}
}
default: 
{
lean_object* v_key_3616_; lean_object* v_entry_x3f_3617_; lean_object* v_children_3618_; lean_object* v_s_3620_; 
v_key_3616_ = lean_ctor_get(v_t_3598_, 0);
v_entry_x3f_3617_ = lean_ctor_get(v_t_3598_, 1);
v_children_3618_ = lean_ctor_get(v_t_3598_, 2);
if (lean_obj_tag(v_entry_x3f_3617_) == 1)
{
lean_object* v_val_3628_; lean_object* v_fst_3629_; lean_object* v___x_3630_; 
v_val_3628_ = lean_ctor_get(v_entry_x3f_3617_, 0);
v_fst_3629_ = lean_ctor_get(v_val_3628_, 0);
v___x_3630_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___lam__0(v_init_3599_, v_key_3616_, v_fst_3629_);
lean_dec(v_init_3599_);
v_s_3620_ = v___x_3630_;
goto v___jp_3619_;
}
else
{
v_s_3620_ = v_init_3599_;
goto v___jp_3619_;
}
v___jp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3621_ = lean_thunk_get_own(v_children_3618_);
v___x_3622_ = lean_unsigned_to_nat(0u);
v___x_3623_ = lean_array_get_size(v___x_3621_);
v___x_3624_ = lean_nat_dec_lt(v___x_3622_, v___x_3623_);
if (v___x_3624_ == 0)
{
lean_dec(v___x_3621_);
return v_s_3620_;
}
else
{
size_t v___x_3625_; size_t v___x_3626_; lean_object* v___x_3627_; 
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = lean_usize_of_nat(v___x_3623_);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg(v___x_3621_, v___x_3625_, v___x_3626_, v_s_3620_);
lean_dec(v___x_3621_);
return v___x_3627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg(lean_object* v_as_3631_, size_t v_i_3632_, size_t v_stop_3633_, lean_object* v_b_3634_){
_start:
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_usize_dec_eq(v_i_3632_, v_stop_3633_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; 
v___x_3636_ = lean_array_uget_borrowed(v_as_3631_, v_i_3632_);
v___x_3637_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg(v___x_3636_, v_b_3634_);
v___x_3638_ = ((size_t)1ULL);
v___x_3639_ = lean_usize_add(v_i_3632_, v___x_3638_);
v_i_3632_ = v___x_3639_;
v_b_3634_ = v___x_3637_;
goto _start;
}
else
{
return v_b_3634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_as_3641_, lean_object* v_i_3642_, lean_object* v_stop_3643_, lean_object* v_b_3644_){
_start:
{
size_t v_i_boxed_3645_; size_t v_stop_boxed_3646_; lean_object* v_res_3647_; 
v_i_boxed_3645_ = lean_unbox_usize(v_i_3642_);
lean_dec(v_i_3642_);
v_stop_boxed_3646_ = lean_unbox_usize(v_stop_3643_);
lean_dec(v_stop_3643_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg(v_as_3641_, v_i_boxed_3645_, v_stop_boxed_3646_, v_b_3644_);
lean_dec_ref(v_as_3641_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg___boxed(lean_object* v_t_3648_, lean_object* v_init_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg(v_t_3648_, v_init_3649_);
lean_dec_ref(v_t_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg(lean_object* v_t_3651_, lean_object* v_init_3652_){
_start:
{
lean_object* v_tree_3653_; lean_object* v___x_3654_; 
v_tree_3653_ = lean_ctor_get(v_t_3651_, 1);
v___x_3654_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg(v_tree_3653_, v_init_3652_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg___boxed(lean_object* v_t_3655_, lean_object* v_init_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg(v_t_3655_, v_init_3656_);
lean_dec_ref(v_t_3655_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size___redArg(lean_object* v_t_3658_){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg(v_t_3658_, v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size___redArg___boxed(lean_object* v_t_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_ImportedConsts_size___redArg(v_t_3661_);
lean_dec_ref(v_t_3661_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size(lean_object* v_00_u03b1_3663_, lean_object* v_t_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_ImportedConsts_size___redArg(v_t_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_size___boxed(lean_object* v_00_u03b1_3666_, lean_object* v_t_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_ImportedConsts_size(v_00_u03b1_3666_, v_t_3667_);
lean_dec_ref(v_t_3667_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0(lean_object* v_00_u03b1_3669_, lean_object* v_t_3670_, lean_object* v_init_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___redArg(v_t_3670_, v_init_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0___boxed(lean_object* v_00_u03b1_3673_, lean_object* v_t_3674_, lean_object* v_init_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0(v_00_u03b1_3673_, v_t_3674_, v_init_3675_);
lean_dec_ref(v_t_3674_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0(lean_object* v_00_u03b1_3677_, lean_object* v_t_3678_, lean_object* v_init_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___redArg(v_t_3678_, v_init_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3681_, lean_object* v_t_3682_, lean_object* v_init_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0(v_00_u03b1_3681_, v_t_3682_, v_init_3683_);
lean_dec_ref(v_t_3682_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3685_, lean_object* v_t_3686_, lean_object* v_init_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___redArg(v_t_3686_, v_init_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3689_, lean_object* v_t_3690_, lean_object* v_init_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1(v_00_u03b1_3689_, v_t_3690_, v_init_3691_);
lean_dec_ref(v_t_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3693_, lean_object* v_as_3694_, size_t v_i_3695_, size_t v_stop_3696_, lean_object* v_b_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___redArg(v_as_3694_, v_i_3695_, v_stop_3696_, v_b_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3699_, lean_object* v_as_3700_, lean_object* v_i_3701_, lean_object* v_stop_3702_, lean_object* v_b_3703_){
_start:
{
size_t v_i_boxed_3704_; size_t v_stop_boxed_3705_; lean_object* v_res_3706_; 
v_i_boxed_3704_ = lean_unbox_usize(v_i_3701_);
lean_dec(v_i_3701_);
v_stop_boxed_3705_ = lean_unbox_usize(v_stop_3702_);
lean_dec(v_stop_3702_);
v_res_3706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__2(v_00_u03b1_3699_, v_as_3700_, v_i_boxed_3704_, v_stop_boxed_3705_, v_b_3703_);
lean_dec_ref(v_as_3700_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3707_, lean_object* v_as_3708_, size_t v_i_3709_, size_t v_stop_3710_, lean_object* v_b_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___redArg(v_as_3708_, v_i_3709_, v_stop_3710_, v_b_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3713_, lean_object* v_as_3714_, lean_object* v_i_3715_, lean_object* v_stop_3716_, lean_object* v_b_3717_){
_start:
{
size_t v_i_boxed_3718_; size_t v_stop_boxed_3719_; lean_object* v_res_3720_; 
v_i_boxed_3718_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_stop_boxed_3719_ = lean_unbox_usize(v_stop_3716_);
lean_dec(v_stop_3716_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_size_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3713_, v_as_3714_, v_i_boxed_3718_, v_stop_boxed_3719_, v_b_3717_);
lean_dec_ref(v_as_3714_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_fold___redArg(lean_object* v_t_3721_, lean_object* v_f_3722_, lean_object* v_init_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(v_t_3721_, v_f_3722_, v_init_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_fold(lean_object* v_00_u03b1_3725_, lean_object* v_00_u03c3_3726_, lean_object* v_t_3727_, lean_object* v_f_3728_, lean_object* v_init_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(v_t_3727_, v_f_3728_, v_init_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldM___redArg(lean_object* v_inst_3731_, lean_object* v_t_3732_, lean_object* v_f_3733_, lean_object* v_init_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_ImportedConsts_foldlM___redArg(v_inst_3731_, v_t_3732_, v_f_3733_, v_init_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldM(lean_object* v_m_3736_, lean_object* v_00_u03b1_3737_, lean_object* v_00_u03c3_3738_, lean_object* v_inst_3739_, lean_object* v_t_3740_, lean_object* v_f_3741_, lean_object* v_init_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_ImportedConsts_foldlM___redArg(v_inst_3739_, v_t_3740_, v_f_3741_, v_init_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg___lam__0(lean_object* v_l_3744_, lean_object* v_n_3745_, lean_object* v_v_3746_){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v_n_3745_);
lean_ctor_set(v___x_3747_, 1, v_v_3746_);
v___x_3748_ = lean_array_push(v_l_3744_, v___x_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_l_3749_, lean_object* v_n_3750_, lean_object* v_v_3751_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v_n_3750_);
lean_ctor_set(v___x_3752_, 1, v_v_3751_);
v___x_3753_ = lean_array_push(v_l_3749_, v___x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_t_3754_, lean_object* v_init_3755_){
_start:
{
switch(lean_obj_tag(v_t_3754_))
{
case 0:
{
lean_object* v_key_3756_; lean_object* v_val_3757_; lean_object* v___x_3758_; 
v_key_3756_ = lean_ctor_get(v_t_3754_, 0);
lean_inc(v_key_3756_);
v_val_3757_ = lean_ctor_get(v_t_3754_, 1);
lean_inc(v_val_3757_);
lean_dec_ref_known(v_t_3754_, 2);
v___x_3758_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg___lam__0(v_init_3755_, v_key_3756_, v_val_3757_);
return v___x_3758_;
}
case 1:
{
lean_object* v_children_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_children_3759_ = lean_ctor_get(v_t_3754_, 1);
lean_inc_ref(v_children_3759_);
lean_dec_ref_known(v_t_3754_, 2);
v___x_3760_ = lean_unsigned_to_nat(0u);
v___x_3761_ = lean_array_get_size(v_children_3759_);
v___x_3762_ = lean_nat_dec_lt(v___x_3760_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_dec_ref(v_children_3759_);
return v_init_3755_;
}
else
{
size_t v___x_3763_; size_t v___x_3764_; lean_object* v___x_3765_; 
v___x_3763_ = ((size_t)0ULL);
v___x_3764_ = lean_usize_of_nat(v___x_3761_);
v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg(v_children_3759_, v___x_3763_, v___x_3764_, v_init_3755_);
lean_dec_ref(v_children_3759_);
return v___x_3765_;
}
}
default: 
{
lean_object* v_key_3766_; lean_object* v_val_3767_; lean_object* v_children_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v_key_3766_ = lean_ctor_get(v_t_3754_, 0);
lean_inc(v_key_3766_);
v_val_3767_ = lean_ctor_get(v_t_3754_, 1);
lean_inc(v_val_3767_);
v_children_3768_ = lean_ctor_get(v_t_3754_, 2);
lean_inc_ref(v_children_3768_);
lean_dec_ref_known(v_t_3754_, 3);
v___x_3769_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg___lam__0(v_init_3755_, v_key_3766_, v_val_3767_);
v___x_3770_ = lean_unsigned_to_nat(0u);
v___x_3771_ = lean_array_get_size(v_children_3768_);
v___x_3772_ = lean_nat_dec_lt(v___x_3770_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_dec_ref(v_children_3768_);
return v___x_3769_;
}
else
{
size_t v___x_3773_; size_t v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = ((size_t)0ULL);
v___x_3774_ = lean_usize_of_nat(v___x_3771_);
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg(v_children_3768_, v___x_3773_, v___x_3774_, v___x_3769_);
lean_dec_ref(v_children_3768_);
return v___x_3775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_as_3776_, size_t v_i_3777_, size_t v_stop_3778_, lean_object* v_b_3779_){
_start:
{
uint8_t v___x_3780_; 
v___x_3780_ = lean_usize_dec_eq(v_i_3777_, v_stop_3778_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v___x_3782_; size_t v___x_3783_; size_t v___x_3784_; 
v___x_3781_ = lean_array_uget_borrowed(v_as_3776_, v_i_3777_);
lean_inc(v___x_3781_);
v___x_3782_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg(v___x_3781_, v_b_3779_);
v___x_3783_ = ((size_t)1ULL);
v___x_3784_ = lean_usize_add(v_i_3777_, v___x_3783_);
v_i_3777_ = v___x_3784_;
v_b_3779_ = v___x_3782_;
goto _start;
}
else
{
return v_b_3779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_3786_, lean_object* v_i_3787_, lean_object* v_stop_3788_, lean_object* v_b_3789_){
_start:
{
size_t v_i_boxed_3790_; size_t v_stop_boxed_3791_; lean_object* v_res_3792_; 
v_i_boxed_3790_ = lean_unbox_usize(v_i_3787_);
lean_dec(v_i_3787_);
v_stop_boxed_3791_ = lean_unbox_usize(v_stop_3788_);
lean_dec(v_stop_3788_);
v_res_3792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg(v_as_3786_, v_i_boxed_3790_, v_stop_boxed_3791_, v_b_3789_);
lean_dec_ref(v_as_3786_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg(lean_object* v_t_3793_, lean_object* v_init_3794_){
_start:
{
switch(lean_obj_tag(v_t_3793_))
{
case 0:
{
lean_object* v_tree_3795_; lean_object* v___x_3796_; 
v_tree_3795_ = lean_ctor_get(v_t_3793_, 1);
lean_inc_ref(v_tree_3795_);
lean_dec_ref_known(v_t_3793_, 2);
v___x_3796_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg(v_tree_3795_, v_init_3794_);
return v___x_3796_;
}
case 1:
{
lean_object* v_key_3797_; lean_object* v_entry_x3f_3798_; lean_object* v_children_3799_; lean_object* v_s_3801_; 
v_key_3797_ = lean_ctor_get(v_t_3793_, 0);
lean_inc(v_key_3797_);
v_entry_x3f_3798_ = lean_ctor_get(v_t_3793_, 1);
lean_inc(v_entry_x3f_3798_);
v_children_3799_ = lean_ctor_get(v_t_3793_, 2);
lean_inc_ref(v_children_3799_);
lean_dec_ref_known(v_t_3793_, 3);
if (lean_obj_tag(v_entry_x3f_3798_) == 1)
{
lean_object* v_val_3808_; lean_object* v_fst_3809_; lean_object* v___x_3810_; 
v_val_3808_ = lean_ctor_get(v_entry_x3f_3798_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v_entry_x3f_3798_, 1);
v_fst_3809_ = lean_ctor_get(v_val_3808_, 0);
lean_inc(v_fst_3809_);
lean_dec(v_val_3808_);
v___x_3810_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg___lam__0(v_init_3794_, v_key_3797_, v_fst_3809_);
v_s_3801_ = v___x_3810_;
goto v___jp_3800_;
}
else
{
lean_dec(v_entry_x3f_3798_);
lean_dec(v_key_3797_);
v_s_3801_ = v_init_3794_;
goto v___jp_3800_;
}
v___jp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3802_ = lean_unsigned_to_nat(0u);
v___x_3803_ = lean_array_get_size(v_children_3799_);
v___x_3804_ = lean_nat_dec_lt(v___x_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec_ref(v_children_3799_);
return v_s_3801_;
}
else
{
size_t v___x_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = ((size_t)0ULL);
v___x_3806_ = lean_usize_of_nat(v___x_3803_);
v___x_3807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg(v_children_3799_, v___x_3805_, v___x_3806_, v_s_3801_);
lean_dec_ref(v_children_3799_);
return v___x_3807_;
}
}
}
default: 
{
lean_object* v_key_3811_; lean_object* v_entry_x3f_3812_; lean_object* v_children_3813_; lean_object* v_s_3815_; 
v_key_3811_ = lean_ctor_get(v_t_3793_, 0);
lean_inc(v_key_3811_);
v_entry_x3f_3812_ = lean_ctor_get(v_t_3793_, 1);
lean_inc(v_entry_x3f_3812_);
v_children_3813_ = lean_ctor_get(v_t_3793_, 2);
lean_inc_ref(v_children_3813_);
lean_dec_ref_known(v_t_3793_, 3);
if (lean_obj_tag(v_entry_x3f_3812_) == 1)
{
lean_object* v_val_3823_; lean_object* v_fst_3824_; lean_object* v___x_3825_; 
v_val_3823_ = lean_ctor_get(v_entry_x3f_3812_, 0);
lean_inc(v_val_3823_);
lean_dec_ref_known(v_entry_x3f_3812_, 1);
v_fst_3824_ = lean_ctor_get(v_val_3823_, 0);
lean_inc(v_fst_3824_);
lean_dec(v_val_3823_);
v___x_3825_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg___lam__0(v_init_3794_, v_key_3811_, v_fst_3824_);
v_s_3815_ = v___x_3825_;
goto v___jp_3814_;
}
else
{
lean_dec(v_entry_x3f_3812_);
lean_dec(v_key_3811_);
v_s_3815_ = v_init_3794_;
goto v___jp_3814_;
}
v___jp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3816_ = lean_thunk_get_own(v_children_3813_);
lean_dec_ref(v_children_3813_);
v___x_3817_ = lean_unsigned_to_nat(0u);
v___x_3818_ = lean_array_get_size(v___x_3816_);
v___x_3819_ = lean_nat_dec_lt(v___x_3817_, v___x_3818_);
if (v___x_3819_ == 0)
{
lean_dec(v___x_3816_);
return v_s_3815_;
}
else
{
size_t v___x_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = lean_usize_of_nat(v___x_3818_);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg(v___x_3816_, v___x_3820_, v___x_3821_, v_s_3815_);
lean_dec(v___x_3816_);
return v___x_3822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg(lean_object* v_as_3826_, size_t v_i_3827_, size_t v_stop_3828_, lean_object* v_b_3829_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_usize_dec_eq(v_i_3827_, v_stop_3828_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; size_t v___x_3833_; size_t v___x_3834_; 
v___x_3831_ = lean_array_uget_borrowed(v_as_3826_, v_i_3827_);
lean_inc(v___x_3831_);
v___x_3832_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg(v___x_3831_, v_b_3829_);
v___x_3833_ = ((size_t)1ULL);
v___x_3834_ = lean_usize_add(v_i_3827_, v___x_3833_);
v_i_3827_ = v___x_3834_;
v_b_3829_ = v___x_3832_;
goto _start;
}
else
{
return v_b_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_as_3836_, lean_object* v_i_3837_, lean_object* v_stop_3838_, lean_object* v_b_3839_){
_start:
{
size_t v_i_boxed_3840_; size_t v_stop_boxed_3841_; lean_object* v_res_3842_; 
v_i_boxed_3840_ = lean_unbox_usize(v_i_3837_);
lean_dec(v_i_3837_);
v_stop_boxed_3841_ = lean_unbox_usize(v_stop_3838_);
lean_dec(v_stop_3838_);
v_res_3842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg(v_as_3836_, v_i_boxed_3840_, v_stop_boxed_3841_, v_b_3839_);
lean_dec_ref(v_as_3836_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0___redArg(lean_object* v_t_3843_, lean_object* v_init_3844_){
_start:
{
lean_object* v_tree_3845_; lean_object* v___x_3846_; 
v_tree_3845_ = lean_ctor_get(v_t_3843_, 1);
lean_inc_ref(v_tree_3845_);
lean_dec_ref(v_t_3843_);
v___x_3846_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg(v_tree_3845_, v_init_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_toArray___redArg(lean_object* v_t_3849_){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = ((lean_object*)(l_Lean_ImportedConsts_toArray___redArg___closed__0));
v___x_3851_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0___redArg(v_t_3849_, v___x_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_toArray(lean_object* v_00_u03b1_3852_, lean_object* v_t_3853_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_ImportedConsts_toArray___redArg(v_t_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0(lean_object* v_00_u03b1_3855_, lean_object* v_t_3856_, lean_object* v_init_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0___redArg(v_t_3856_, v_init_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0(lean_object* v_00_u03b1_3859_, lean_object* v_t_3860_, lean_object* v_init_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0___redArg(v_t_3860_, v_init_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3863_, lean_object* v_t_3864_, lean_object* v_init_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1___redArg(v_t_3864_, v_init_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3867_, lean_object* v_as_3868_, size_t v_i_3869_, size_t v_stop_3870_, lean_object* v_b_3871_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___redArg(v_as_3868_, v_i_3869_, v_stop_3870_, v_b_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3873_, lean_object* v_as_3874_, lean_object* v_i_3875_, lean_object* v_stop_3876_, lean_object* v_b_3877_){
_start:
{
size_t v_i_boxed_3878_; size_t v_stop_boxed_3879_; lean_object* v_res_3880_; 
v_i_boxed_3878_ = lean_unbox_usize(v_i_3875_);
lean_dec(v_i_3875_);
v_stop_boxed_3879_ = lean_unbox_usize(v_stop_3876_);
lean_dec(v_stop_3876_);
v_res_3880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__2(v_00_u03b1_3873_, v_as_3874_, v_i_boxed_3878_, v_stop_boxed_3879_, v_b_3877_);
lean_dec_ref(v_as_3874_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3881_, lean_object* v_as_3882_, size_t v_i_3883_, size_t v_stop_3884_, lean_object* v_b_3885_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___redArg(v_as_3882_, v_i_3883_, v_stop_3884_, v_b_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3887_, lean_object* v_as_3888_, lean_object* v_i_3889_, lean_object* v_stop_3890_, lean_object* v_b_3891_){
_start:
{
size_t v_i_boxed_3892_; size_t v_stop_boxed_3893_; lean_object* v_res_3894_; 
v_i_boxed_3892_ = lean_unbox_usize(v_i_3889_);
lean_dec(v_i_3889_);
v_stop_boxed_3893_ = lean_unbox_usize(v_stop_3890_);
lean_dec(v_stop_3890_);
v_res_3894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_toArray_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3887_, v_as_3888_, v_i_boxed_3892_, v_stop_boxed_3893_, v_b_3891_);
lean_dec_ref(v_as_3888_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1___redArg(lean_object* v_t_3895_, lean_object* v_init_3896_){
_start:
{
switch(lean_obj_tag(v_t_3895_))
{
case 0:
{
lean_object* v_val_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
v_val_3897_ = lean_ctor_get(v_t_3895_, 1);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_t_3895_);
if (v_isSharedCheck_3904_ == 0)
{
lean_object* v_unused_3905_; 
v_unused_3905_ = lean_ctor_get(v_t_3895_, 0);
lean_dec(v_unused_3905_);
v___x_3899_ = v_t_3895_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_val_3897_);
lean_dec(v_t_3895_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set_tag(v___x_3899_, 1);
lean_ctor_set(v___x_3899_, 1, v_init_3896_);
lean_ctor_set(v___x_3899_, 0, v_val_3897_);
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_val_3897_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_init_3896_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
case 1:
{
lean_object* v_children_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_children_3906_ = lean_ctor_get(v_t_3895_, 1);
lean_inc_ref(v_children_3906_);
lean_dec_ref_known(v_t_3895_, 2);
v___x_3907_ = lean_unsigned_to_nat(0u);
v___x_3908_ = lean_array_get_size(v_children_3906_);
v___x_3909_ = lean_nat_dec_lt(v___x_3907_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_dec_ref(v_children_3906_);
return v_init_3896_;
}
else
{
size_t v___x_3910_; size_t v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = ((size_t)0ULL);
v___x_3911_ = lean_usize_of_nat(v___x_3908_);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg(v_children_3906_, v___x_3910_, v___x_3911_, v_init_3896_);
lean_dec_ref(v_children_3906_);
return v___x_3912_;
}
}
default: 
{
lean_object* v_val_3913_; lean_object* v_children_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; 
v_val_3913_ = lean_ctor_get(v_t_3895_, 1);
lean_inc(v_val_3913_);
v_children_3914_ = lean_ctor_get(v_t_3895_, 2);
lean_inc_ref(v_children_3914_);
lean_dec_ref_known(v_t_3895_, 3);
v___x_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3915_, 0, v_val_3913_);
lean_ctor_set(v___x_3915_, 1, v_init_3896_);
v___x_3916_ = lean_unsigned_to_nat(0u);
v___x_3917_ = lean_array_get_size(v_children_3914_);
v___x_3918_ = lean_nat_dec_lt(v___x_3916_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_dec_ref(v_children_3914_);
return v___x_3915_;
}
else
{
size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = ((size_t)0ULL);
v___x_3920_ = lean_usize_of_nat(v___x_3917_);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg(v_children_3914_, v___x_3919_, v___x_3920_, v___x_3915_);
lean_dec_ref(v_children_3914_);
return v___x_3921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_as_3922_, size_t v_i_3923_, size_t v_stop_3924_, lean_object* v_b_3925_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_usize_dec_eq(v_i_3923_, v_stop_3924_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; lean_object* v___x_3928_; size_t v___x_3929_; size_t v___x_3930_; 
v___x_3927_ = lean_array_uget_borrowed(v_as_3922_, v_i_3923_);
lean_inc(v___x_3927_);
v___x_3928_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1___redArg(v___x_3927_, v_b_3925_);
v___x_3929_ = ((size_t)1ULL);
v___x_3930_ = lean_usize_add(v_i_3923_, v___x_3929_);
v_i_3923_ = v___x_3930_;
v_b_3925_ = v___x_3928_;
goto _start;
}
else
{
return v_b_3925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_3932_, lean_object* v_i_3933_, lean_object* v_stop_3934_, lean_object* v_b_3935_){
_start:
{
size_t v_i_boxed_3936_; size_t v_stop_boxed_3937_; lean_object* v_res_3938_; 
v_i_boxed_3936_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_stop_boxed_3937_ = lean_unbox_usize(v_stop_3934_);
lean_dec(v_stop_3934_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg(v_as_3932_, v_i_boxed_3936_, v_stop_boxed_3937_, v_b_3935_);
lean_dec_ref(v_as_3932_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0___redArg(lean_object* v_t_3939_, lean_object* v_init_3940_){
_start:
{
switch(lean_obj_tag(v_t_3939_))
{
case 0:
{
lean_object* v_tree_3941_; lean_object* v___x_3942_; 
v_tree_3941_ = lean_ctor_get(v_t_3939_, 1);
lean_inc_ref(v_tree_3941_);
lean_dec_ref_known(v_t_3939_, 2);
v___x_3942_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1___redArg(v_tree_3941_, v_init_3940_);
return v___x_3942_;
}
case 1:
{
lean_object* v_entry_x3f_3943_; lean_object* v_children_3944_; lean_object* v_s_3946_; 
v_entry_x3f_3943_ = lean_ctor_get(v_t_3939_, 1);
lean_inc(v_entry_x3f_3943_);
v_children_3944_ = lean_ctor_get(v_t_3939_, 2);
lean_inc_ref(v_children_3944_);
lean_dec_ref_known(v_t_3939_, 3);
if (lean_obj_tag(v_entry_x3f_3943_) == 1)
{
lean_object* v_val_3953_; lean_object* v_fst_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
v_val_3953_ = lean_ctor_get(v_entry_x3f_3943_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v_entry_x3f_3943_, 1);
v_fst_3954_ = lean_ctor_get(v_val_3953_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_val_3953_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; 
v_unused_3962_ = lean_ctor_get(v_val_3953_, 1);
lean_dec(v_unused_3962_);
v___x_3956_ = v_val_3953_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_fst_3954_);
lean_dec(v_val_3953_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
lean_ctor_set_tag(v___x_3956_, 1);
lean_ctor_set(v___x_3956_, 1, v_init_3940_);
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_fst_3954_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_init_3940_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
v_s_3946_ = v___x_3959_;
goto v___jp_3945_;
}
}
}
else
{
lean_dec(v_entry_x3f_3943_);
v_s_3946_ = v_init_3940_;
goto v___jp_3945_;
}
v___jp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3947_ = lean_unsigned_to_nat(0u);
v___x_3948_ = lean_array_get_size(v_children_3944_);
v___x_3949_ = lean_nat_dec_lt(v___x_3947_, v___x_3948_);
if (v___x_3949_ == 0)
{
lean_dec_ref(v_children_3944_);
return v_s_3946_;
}
else
{
size_t v___x_3950_; size_t v___x_3951_; lean_object* v___x_3952_; 
v___x_3950_ = ((size_t)0ULL);
v___x_3951_ = lean_usize_of_nat(v___x_3948_);
v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg(v_children_3944_, v___x_3950_, v___x_3951_, v_s_3946_);
lean_dec_ref(v_children_3944_);
return v___x_3952_;
}
}
}
default: 
{
lean_object* v_entry_x3f_3963_; lean_object* v_children_3964_; lean_object* v_s_3966_; 
v_entry_x3f_3963_ = lean_ctor_get(v_t_3939_, 1);
lean_inc(v_entry_x3f_3963_);
v_children_3964_ = lean_ctor_get(v_t_3939_, 2);
lean_inc_ref(v_children_3964_);
lean_dec_ref_known(v_t_3939_, 3);
if (lean_obj_tag(v_entry_x3f_3963_) == 1)
{
lean_object* v_val_3974_; lean_object* v_fst_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
v_val_3974_ = lean_ctor_get(v_entry_x3f_3963_, 0);
lean_inc(v_val_3974_);
lean_dec_ref_known(v_entry_x3f_3963_, 1);
v_fst_3975_ = lean_ctor_get(v_val_3974_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_val_3974_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; 
v_unused_3983_ = lean_ctor_get(v_val_3974_, 1);
lean_dec(v_unused_3983_);
v___x_3977_ = v_val_3974_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_fst_3975_);
lean_dec(v_val_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set_tag(v___x_3977_, 1);
lean_ctor_set(v___x_3977_, 1, v_init_3940_);
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_fst_3975_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_init_3940_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
v_s_3966_ = v___x_3980_;
goto v___jp_3965_;
}
}
}
else
{
lean_dec(v_entry_x3f_3963_);
v_s_3966_ = v_init_3940_;
goto v___jp_3965_;
}
v___jp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3967_ = lean_thunk_get_own(v_children_3964_);
lean_dec_ref(v_children_3964_);
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = lean_array_get_size(v___x_3967_);
v___x_3970_ = lean_nat_dec_lt(v___x_3968_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_dec(v___x_3967_);
return v_s_3966_;
}
else
{
size_t v___x_3971_; size_t v___x_3972_; lean_object* v___x_3973_; 
v___x_3971_ = ((size_t)0ULL);
v___x_3972_ = lean_usize_of_nat(v___x_3969_);
v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg(v___x_3967_, v___x_3971_, v___x_3972_, v_s_3966_);
lean_dec(v___x_3967_);
return v___x_3973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg(lean_object* v_as_3984_, size_t v_i_3985_, size_t v_stop_3986_, lean_object* v_b_3987_){
_start:
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_usize_dec_eq(v_i_3985_, v_stop_3986_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; size_t v___x_3991_; size_t v___x_3992_; 
v___x_3989_ = lean_array_uget_borrowed(v_as_3984_, v_i_3985_);
lean_inc(v___x_3989_);
v___x_3990_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0___redArg(v___x_3989_, v_b_3987_);
v___x_3991_ = ((size_t)1ULL);
v___x_3992_ = lean_usize_add(v_i_3985_, v___x_3991_);
v_i_3985_ = v___x_3992_;
v_b_3987_ = v___x_3990_;
goto _start;
}
else
{
return v_b_3987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_as_3994_, lean_object* v_i_3995_, lean_object* v_stop_3996_, lean_object* v_b_3997_){
_start:
{
size_t v_i_boxed_3998_; size_t v_stop_boxed_3999_; lean_object* v_res_4000_; 
v_i_boxed_3998_ = lean_unbox_usize(v_i_3995_);
lean_dec(v_i_3995_);
v_stop_boxed_3999_ = lean_unbox_usize(v_stop_3996_);
lean_dec(v_stop_3996_);
v_res_4000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg(v_as_3994_, v_i_boxed_3998_, v_stop_boxed_3999_, v_b_3997_);
lean_dec_ref(v_as_3994_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0___redArg(lean_object* v_t_4001_, lean_object* v_init_4002_){
_start:
{
lean_object* v_tree_4003_; lean_object* v___x_4004_; 
v_tree_4003_ = lean_ctor_get(v_t_4001_, 1);
lean_inc_ref(v_tree_4003_);
lean_dec_ref(v_t_4001_);
v___x_4004_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0___redArg(v_tree_4003_, v_init_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_values___redArg(lean_object* v_t_4005_){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_box(0);
v___x_4007_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0___redArg(v_t_4005_, v___x_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_values(lean_object* v_00_u03b1_4008_, lean_object* v_t_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_ImportedConsts_values___redArg(v_t_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0(lean_object* v_00_u03b1_4011_, lean_object* v_t_4012_, lean_object* v_init_4013_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0___redArg(v_t_4012_, v_init_4013_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0(lean_object* v_00_u03b1_4015_, lean_object* v_t_4016_, lean_object* v_init_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0___redArg(v_t_4016_, v_init_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4019_, lean_object* v_t_4020_, lean_object* v_init_4021_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1___redArg(v_t_4020_, v_init_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_4023_, lean_object* v_as_4024_, size_t v_i_4025_, size_t v_stop_4026_, lean_object* v_b_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___redArg(v_as_4024_, v_i_4025_, v_stop_4026_, v_b_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4029_, lean_object* v_as_4030_, lean_object* v_i_4031_, lean_object* v_stop_4032_, lean_object* v_b_4033_){
_start:
{
size_t v_i_boxed_4034_; size_t v_stop_boxed_4035_; lean_object* v_res_4036_; 
v_i_boxed_4034_ = lean_unbox_usize(v_i_4031_);
lean_dec(v_i_4031_);
v_stop_boxed_4035_ = lean_unbox_usize(v_stop_4032_);
lean_dec(v_stop_4032_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__2(v_00_u03b1_4029_, v_as_4030_, v_i_boxed_4034_, v_stop_boxed_4035_, v_b_4033_);
lean_dec_ref(v_as_4030_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_4037_, lean_object* v_as_4038_, size_t v_i_4039_, size_t v_stop_4040_, lean_object* v_b_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___redArg(v_as_4038_, v_i_4039_, v_stop_4040_, v_b_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4043_, lean_object* v_as_4044_, lean_object* v_i_4045_, lean_object* v_stop_4046_, lean_object* v_b_4047_){
_start:
{
size_t v_i_boxed_4048_; size_t v_stop_boxed_4049_; lean_object* v_res_4050_; 
v_i_boxed_4048_ = lean_unbox_usize(v_i_4045_);
lean_dec(v_i_4045_);
v_stop_boxed_4049_ = lean_unbox_usize(v_stop_4046_);
lean_dec(v_stop_4046_);
v_res_4050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00Lean_ImportedConsts_values_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_4043_, v_as_4044_, v_i_boxed_4048_, v_stop_boxed_4049_, v_b_4047_);
lean_dec_ref(v_as_4044_);
return v_res_4050_;
}
}
static lean_object* _init_l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4054_ = ((lean_object*)(l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__2));
v___x_4055_ = lean_unsigned_to_nat(14u);
v___x_4056_ = lean_unsigned_to_nat(22u);
v___x_4057_ = ((lean_object*)(l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__1));
v___x_4058_ = ((lean_object*)(l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__0));
v___x_4059_ = l_mkPanicMessageWithDecl(v___x_4058_, v___x_4057_, v___x_4056_, v___x_4055_, v___x_4054_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0(lean_object* v_inst_4060_, lean_object* v_t_4061_, lean_object* v_n_4062_, lean_object* v_x_4063_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lean_ImportedConsts_find_x3f___redArg(v_t_4061_, v_n_4062_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_obj_once(&l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__3, &l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__3_once, _init_l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___closed__3);
v___x_4066_ = l_panic___redArg(v_inst_4060_, v___x_4065_);
return v___x_4066_;
}
else
{
lean_object* v_val_4067_; 
v_val_4067_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_val_4067_);
lean_dec_ref_known(v___x_4064_, 1);
return v_val_4067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___boxed(lean_object* v_inst_4068_, lean_object* v_t_4069_, lean_object* v_n_4070_, lean_object* v_x_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0(v_inst_4068_, v_t_4069_, v_n_4070_, v_x_4071_);
lean_dec(v_inst_4068_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__1(lean_object* v_inst_4073_, lean_object* v_xs_4074_, lean_object* v_i_4075_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_ImportedConsts_find_x3f___redArg(v_xs_4074_, v_i_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v___x_4077_; 
v___x_4077_ = l_outOfBounds___redArg(v_inst_4073_);
return v___x_4077_;
}
else
{
lean_object* v_val_4078_; 
v_val_4078_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_val_4078_);
lean_dec_ref_known(v___x_4076_, 1);
return v_val_4078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__1___boxed(lean_object* v_inst_4079_, lean_object* v_xs_4080_, lean_object* v_i_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__1(v_inst_4079_, v_xs_4080_, v_i_4081_);
lean_dec(v_inst_4079_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg(lean_object* v_inst_4085_){
_start:
{
lean_object* v___f_4086_; lean_object* v___f_4087_; lean_object* v___f_4088_; lean_object* v___x_4089_; 
v___f_4086_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4086_, 0, v_inst_4085_);
v___f_4087_ = ((lean_object*)(l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__0));
v___f_4088_ = ((lean_object*)(l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg___closed__1));
v___x_4089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4089_, 0, v___f_4086_);
lean_ctor_set(v___x_4089_, 1, v___f_4087_);
lean_ctor_set(v___x_4089_, 2, v___f_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited(lean_object* v_00_u03b1_4090_, lean_object* v_inst_4091_){
_start:
{
lean_object* v___x_4092_; 
v___x_4092_ = l_Lean_ImportedConsts_instGetElem_x3fNameTrueOfInhabited___redArg(v_inst_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__0(lean_object* v_f_4093_, lean_object* v_n_4094_, lean_object* v_v_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v_n_4094_);
lean_ctor_set(v___x_4096_, 1, v_v_4095_);
v___x_4097_ = lean_apply_1(v_f_4093_, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__1(lean_object* v_inst_4098_, lean_object* v_t_4099_, lean_object* v_f_4100_){
_start:
{
lean_object* v___f_4101_; lean_object* v___x_4102_; 
v___f_4101_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4101_, 0, v_f_4100_);
v___x_4102_ = l_Lean_ImportedConsts_forM___redArg(v_inst_4098_, v_t_4099_, v___f_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg(lean_object* v_inst_4103_){
_start:
{
lean_object* v___f_4104_; 
v___f_4104_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_4104_, 0, v_inst_4103_);
return v___f_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForMProdNameOfMonad(lean_object* v_m_4105_, lean_object* v_00_u03b1_4106_, lean_object* v_inst_4107_){
_start:
{
lean_object* v___f_4108_; 
v___f_4108_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForMProdNameOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_4108_, 0, v_inst_4107_);
return v___f_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__0(lean_object* v_toPure_4109_, lean_object* v_____do__lift_4110_){
_start:
{
if (lean_obj_tag(v_____do__lift_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4112_; 
v_a_4111_ = lean_ctor_get(v_____do__lift_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v_____do__lift_4110_, 1);
v___x_4112_ = lean_apply_2(v_toPure_4109_, lean_box(0), v_a_4111_);
return v___x_4112_;
}
else
{
lean_object* v_a_4113_; lean_object* v_snd_4114_; lean_object* v___x_4115_; 
v_a_4113_ = lean_ctor_get(v_____do__lift_4110_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v_____do__lift_4110_, 1);
v_snd_4114_ = lean_ctor_get(v_a_4113_, 1);
lean_inc(v_snd_4114_);
lean_dec(v_a_4113_);
v___x_4115_ = lean_apply_2(v_toPure_4109_, lean_box(0), v_snd_4114_);
return v___x_4115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__1(lean_object* v_toPure_4116_, lean_object* v_____do__lift_4117_){
_start:
{
if (lean_obj_tag(v_____do__lift_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4126_; 
v_a_4118_ = lean_ctor_get(v_____do__lift_4117_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_____do__lift_4117_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4120_ = v_____do__lift_4117_;
v_isShared_4121_ = v_isSharedCheck_4126_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v_____do__lift_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4126_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_apply_2(v_toPure_4116_, lean_box(0), v___x_4123_);
return v___x_4124_;
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4137_; 
v_a_4127_ = lean_ctor_get(v_____do__lift_4117_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_____do__lift_4117_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4129_ = v_____do__lift_4117_;
v_isShared_4130_ = v_isSharedCheck_4137_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v_____do__lift_4117_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4137_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4131_ = lean_box(0);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v_a_4127_);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v___x_4132_);
v___x_4134_ = v___x_4129_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_apply_2(v_toPure_4116_, lean_box(0), v___x_4134_);
return v___x_4135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__2(lean_object* v___y_4138_, lean_object* v_toBind_4139_, lean_object* v___f_4140_, lean_object* v_n_4141_, lean_object* v_v_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4144_, 0, v_n_4141_);
lean_ctor_set(v___x_4144_, 1, v_v_4142_);
v___x_4145_ = lean_apply_2(v___y_4138_, v___x_4144_, v___y_4143_);
v___x_4146_ = lean_apply_4(v_toBind_4139_, lean_box(0), lean_box(0), v___x_4145_, v___f_4140_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__3(lean_object* v_inst_4147_, lean_object* v_00_u03b2_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___f_4152_; lean_object* v___f_4153_; lean_object* v___f_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___f_4162_; lean_object* v___f_4163_; lean_object* v___f_4164_; lean_object* v___f_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v_toApplicative_4172_; lean_object* v_toBind_4173_; lean_object* v_toPure_4174_; lean_object* v___f_4175_; lean_object* v___f_4176_; lean_object* v___f_4177_; lean_object* v___x_138__overap_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_inc_ref_n(v_inst_4147_, 7);
v___f_4152_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_4152_, 0, v_inst_4147_);
v___f_4153_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_4153_, 0, v_inst_4147_);
v___f_4154_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_4154_, 0, v_inst_4147_);
v___f_4155_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_4155_, 0, v_inst_4147_);
v___x_4156_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_4156_, 0, lean_box(0));
lean_closure_set(v___x_4156_, 1, lean_box(0));
lean_closure_set(v___x_4156_, 2, v_inst_4147_);
v___x_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
lean_ctor_set(v___x_4157_, 1, v___f_4152_);
v___x_4158_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_4158_, 0, lean_box(0));
lean_closure_set(v___x_4158_, 1, lean_box(0));
lean_closure_set(v___x_4158_, 2, v_inst_4147_);
v___x_4159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
lean_ctor_set(v___x_4159_, 2, v___f_4153_);
lean_ctor_set(v___x_4159_, 3, v___f_4154_);
lean_ctor_set(v___x_4159_, 4, v___f_4155_);
v___x_4160_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_4160_, 0, lean_box(0));
lean_closure_set(v___x_4160_, 1, lean_box(0));
lean_closure_set(v___x_4160_, 2, v_inst_4147_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
lean_inc_ref_n(v___x_4161_, 6);
v___f_4162_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4162_, 0, v___x_4161_);
v___f_4163_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4163_, 0, v___x_4161_);
v___f_4164_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_4164_, 0, v___x_4161_);
v___f_4165_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_4165_, 0, v___x_4161_);
v___x_4166_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_4166_, 0, lean_box(0));
lean_closure_set(v___x_4166_, 1, lean_box(0));
lean_closure_set(v___x_4166_, 2, v___x_4161_);
v___x_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v___f_4162_);
v___x_4168_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_4168_, 0, lean_box(0));
lean_closure_set(v___x_4168_, 1, lean_box(0));
lean_closure_set(v___x_4168_, 2, v___x_4161_);
v___x_4169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4167_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
lean_ctor_set(v___x_4169_, 2, v___f_4163_);
lean_ctor_set(v___x_4169_, 3, v___f_4164_);
lean_ctor_set(v___x_4169_, 4, v___f_4165_);
v___x_4170_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_4170_, 0, lean_box(0));
lean_closure_set(v___x_4170_, 1, lean_box(0));
lean_closure_set(v___x_4170_, 2, v___x_4161_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v_toApplicative_4172_ = lean_ctor_get(v_inst_4147_, 0);
lean_inc_ref(v_toApplicative_4172_);
v_toBind_4173_ = lean_ctor_get(v_inst_4147_, 1);
lean_inc_n(v_toBind_4173_, 2);
lean_dec_ref(v_inst_4147_);
v_toPure_4174_ = lean_ctor_get(v_toApplicative_4172_, 1);
lean_inc_n(v_toPure_4174_, 2);
lean_dec_ref(v_toApplicative_4172_);
v___f_4175_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4175_, 0, v_toPure_4174_);
v___f_4176_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4176_, 0, v_toPure_4174_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_4177_, 0, v___y_4151_);
lean_closure_set(v___f_4177_, 1, v_toBind_4173_);
lean_closure_set(v___f_4177_, 2, v___f_4176_);
v___x_138__overap_4178_ = l_Lean_ImportedConsts_forM___redArg(v___x_4171_, v___y_4149_, v___f_4177_);
v___x_4179_ = lean_apply_1(v___x_138__overap_4178_, v___y_4150_);
v___x_4180_ = lean_apply_4(v_toBind_4173_, lean_box(0), lean_box(0), v___x_4179_, v___f_4175_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg(lean_object* v_inst_4181_){
_start:
{
lean_object* v___f_4182_; 
v___f_4182_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_4182_, 0, v_inst_4181_);
return v___f_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_instForInProdNameOfMonad(lean_object* v_m_4183_, lean_object* v_00_u03b1_4184_, lean_object* v_inst_4185_){
_start:
{
lean_object* v___f_4186_; 
v___f_4186_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_instForInProdNameOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_4186_, 0, v_inst_4185_);
return v___f_4186_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ConstTrie(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_ConstTrie_0__Lean_LookupCacheImpl = _init_l___private_Lean_ConstTrie_0__Lean_LookupCacheImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ConstTrie(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ConstTrie(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ConstTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ConstTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ConstTrie(builtin);
}
#ifdef __cplusplus
}
#endif
