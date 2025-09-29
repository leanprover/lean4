// Lean compiler output
// Module: Lean.Util.PtrSet
// Imports: Init.Data.Hashable Std.Data.HashSet.Basic Std.Data.HashMap.Basic
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
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object*);
static lean_object* l_Lean_PtrSet_insert___redArg___closed__1;
static lean_object* l_Lean_PtrSet_insert___redArg___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Ptr_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Ptr_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Ptr_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Ptr_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Ptr_ctorIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = 11;
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_instHashablePtr___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqPtr___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPtrSet___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrSet___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPtrSet(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PtrSet_insert___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PtrSet_insert___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_PtrSet_insert___redArg___closed__0;
x_4 = l_Lean_PtrSet_insert___redArg___closed__1;
x_5 = lean_box(0);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(x_3, x_4, x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_PtrSet_insert___redArg___closed__0;
x_5 = l_Lean_PtrSet_insert___redArg___closed__1;
x_6 = lean_box(0);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(x_4, x_5, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_PtrSet_insert___redArg___closed__0;
x_4 = l_Lean_PtrSet_insert___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_PtrSet_insert___redArg___closed__0;
x_5 = l_Lean_PtrSet_insert___redArg___closed__1;
x_6 = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(x_4, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrSet_contains___redArg(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PtrSet_contains(x_1, x_2, x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkPtrMap___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrMap___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkPtrMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_PtrSet_insert___redArg___closed__0;
x_5 = l_Lean_PtrSet_insert___redArg___closed__1;
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_PtrSet_insert___redArg___closed__0;
x_7 = l_Lean_PtrSet_insert___redArg___closed__1;
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_PtrSet_insert___redArg___closed__0;
x_4 = l_Lean_PtrSet_insert___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_PtrSet_insert___redArg___closed__0;
x_6 = l_Lean_PtrSet_insert___redArg___closed__1;
x_7 = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrMap_contains___redArg(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_PtrMap_contains(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_PtrSet_insert___redArg___closed__0;
x_4 = l_Lean_PtrSet_insert___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_PtrSet_insert___redArg___closed__0;
x_6 = l_Lean_PtrSet_insert___redArg___closed__1;
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PtrMap_find_x3f___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PtrMap_find_x3f(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PtrSet_insert___redArg___closed__0 = _init_l_Lean_PtrSet_insert___redArg___closed__0();
lean_mark_persistent(l_Lean_PtrSet_insert___redArg___closed__0);
l_Lean_PtrSet_insert___redArg___closed__1 = _init_l_Lean_PtrSet_insert___redArg___closed__1();
lean_mark_persistent(l_Lean_PtrSet_insert___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
