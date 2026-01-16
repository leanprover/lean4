// Lean compiler output
// Module: Lean.Compiler.IR.Toposort
// Imports: public import Lean.Compiler.IR.CompilerM
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
static lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_toposortDecls___closed__0;
static lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__0;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toposortDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toposortDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_toposortDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Decl_isExtern(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toposortDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_toposortDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__0(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1;
x_18 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2;
lean_inc_ref(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = lean_box(0);
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, lean_box(0));
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1;
x_35 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2;
lean_inc_ref(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = lean_box(0);
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, lean_box(0));
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1;
x_55 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2;
lean_inc_ref(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = lean_box(0);
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, lean_box(0));
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5_spec__8___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.IR.Toposort.0.Lean.IR.toposort.process", 61, 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.Toposort", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__2;
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_unsigned_to_nat(44u);
x_4 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__1;
x_5 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_Decl_name(x_1);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg(x_7, x_8);
lean_dec_ref(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_take(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_box(0);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1___redArg(x_12, x_8, x_13);
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_2, x_10);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_16);
x_17 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(x_16, x_2, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_st_ref_take(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 2);
x_23 = lean_array_push(x_22, x_1);
lean_ctor_set(x_20, 2, x_23);
x_24 = lean_st_ref_set(x_2, x_20);
lean_dec(x_2);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
x_27 = lean_ctor_get(x_20, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_28 = lean_array_push(x_27, x_1);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_st_ref_set(x_2, x_29);
lean_dec(x_2);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
x_31 = lean_st_ref_take(x_2);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc_ref(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = lean_array_push(x_34, x_1);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 3, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_st_ref_set(x_2, x_37);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_13);
return x_39;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_1);
x_40 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3;
x_41 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2(x_40, x_2, x_3, x_4);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
x_44 = lean_ctor_get(x_10, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_45 = lean_box(0);
x_46 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1___redArg(x_43, x_8, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_44);
x_48 = lean_st_ref_set(x_2, x_47);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_49);
x_50 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(x_49, x_2, x_3, x_4);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_51 = x_50;
} else {
 lean_dec_ref(x_50);
 x_51 = lean_box(0);
}
x_52 = lean_st_ref_take(x_2);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_array_push(x_55, x_1);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 3, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_st_ref_set(x_2, x_58);
lean_dec(x_2);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_45);
return x_60;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_50;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_1);
x_61 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3;
x_62 = l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2(x_61, x_2, x_3, x_4);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec_ref(x_1);
switch (lean_obj_tag(x_6)) {
case 6:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec_ref(x_6);
x_8 = x_21;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = lean_box(0);
goto block_20;
}
case 7:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec_ref(x_6);
x_8 = x_22;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = lean_box(0);
goto block_20;
}
default: 
{
lean_dec_ref(x_6);
x_1 = x_7;
goto _start;
}
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_st_ref_get(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg(x_14, x_8);
lean_dec(x_8);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_17 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process(x_16, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_1 = x_7;
x_2 = x_9;
x_3 = x_10;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_17;
}
}
else
{
lean_dec(x_15);
x_1 = x_7;
x_2 = x_9;
x_3 = x_10;
x_4 = x_11;
goto _start;
}
}
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_dec_ref(x_1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_26 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(x_24, x_2, x_3, x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
x_1 = x_25;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_26;
}
}
case 9:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_28);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
if (x_32 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_30);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5(x_28, x_36, x_37, x_31, x_2, x_3, x_4);
lean_dec_ref(x_28);
return x_38;
}
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_30);
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5(x_28, x_39, x_40, x_31, x_2, x_3, x_4);
lean_dec_ref(x_28);
return x_41;
}
}
}
case 11:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
case 10:
{
uint8_t x_44; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_46);
return x_1;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
case 12:
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
default: 
{
lean_object* x_51; 
x_51 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_51;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_2);
x_11 = l_Lean_IR_Alt_body(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__5(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_processBody_spec__4_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2_spec__5_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_11 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process(x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
if (x_9 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0(x_1, x_13, x_14, x_8, x_2, x_3, x_4);
return x_15;
}
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_7);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go_spec__0(x_1, x_16, x_17, x_8, x_2, x_3, x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Name_hash___override(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__1_spec__2___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1___redArg(x_2, x_5, x_6);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_IR_Decl_name(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_IR_Decl_name(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_1);
x_5 = lean_array_to_list(x_1);
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__0(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_box(0);
x_10 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__1;
x_11 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___redArg(x_7, x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_nat_mul(x_12, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_mk_array(x_17, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_empty_array_with_capacity(x_12);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_mk_ref(x_21);
lean_inc(x_22);
x_23 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_go(x_1, x_22, x_2, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_st_ref_get(x_22);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_27);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_28 = lean_st_ref_get(x_22);
lean_dec(x_22);
x_29 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toposortDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
return x_4;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_array_uget(x_1, x_3);
x_15 = l_Lean_IR_Decl_isExtern(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_push(x_13, x_14);
lean_ctor_set(x_4, 1, x_16);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_12, x_14);
lean_ctor_set(x_4, 0, x_17);
x_5 = x_4;
goto block_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_array_uget(x_1, x_3);
x_21 = l_Lean_IR_Decl_isExtern(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_push(x_19, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_5 = x_23;
goto block_9;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_array_push(x_18, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
x_5 = x_25;
goto block_9;
}
}
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_3, x_6);
x_3 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toposortDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toposortDecls_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_toposortDecls___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_toposortDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_toposortDecls___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toposortDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_IR_toposortDecls___closed__1;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toposortDecls_spec__0(x_1, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort(x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Array_append___redArg(x_9, x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Array_append___redArg(x_9, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toposortDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toposortDecls(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Toposort(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__0 = _init_l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__0);
l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1 = _init_l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1();
lean_mark_persistent(l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__1);
l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2 = _init_l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2();
lean_mark_persistent(l_panic___at___00__private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process_spec__2___closed__2);
l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__2 = _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__2);
l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__1 = _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__1);
l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__0 = _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__0);
l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3 = _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort_process___closed__3);
l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__0 = _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__0);
l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__1 = _init_l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Toposort_0__Lean_IR_toposort___closed__1);
l_Lean_IR_toposortDecls___closed__0 = _init_l_Lean_IR_toposortDecls___closed__0();
lean_mark_persistent(l_Lean_IR_toposortDecls___closed__0);
l_Lean_IR_toposortDecls___closed__1 = _init_l_Lean_IR_toposortDecls___closed__1();
lean_mark_persistent(l_Lean_IR_toposortDecls___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
