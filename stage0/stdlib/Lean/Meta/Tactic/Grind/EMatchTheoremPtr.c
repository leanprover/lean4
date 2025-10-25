// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EMatchTheoremPtr
// Imports: public import Lean.Meta.Tactic.Grind.EMatchTheorem
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
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSameEMatchTheoremPtr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremPtr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isSameEMatchTheoremPtr(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0___boxed(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremPtr_ctorIdx(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isSameEMatchTheoremPtr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSameEMatchTheoremPtr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_isSameEMatchTheoremPtr(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremPtr_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremPtr_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_EMatchTheoremPtr_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; uint64_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = 3;
x_4 = lean_usize_shift_right(x_2, x_3);
x_5 = lean_usize_to_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_hashEMatchTheoremPtr(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instHashableEMatchTheoremPtr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqEMatchTheoremPtr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instHashableEMatchTheoremPtr = _init_l_Lean_Meta_Grind_instHashableEMatchTheoremPtr();
lean_mark_persistent(l_Lean_Meta_Grind_instHashableEMatchTheoremPtr);
l_Lean_Meta_Grind_instBEqEMatchTheoremPtr = _init_l_Lean_Meta_Grind_instBEqEMatchTheoremPtr();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqEMatchTheoremPtr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
