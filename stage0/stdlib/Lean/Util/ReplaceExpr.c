// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: Init Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__14;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor___boxed(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
static size_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__1;
static uint8_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__7;
uint32_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_hasResultFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_keyIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___boxed(lean_object*);
static size_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__8;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static size_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__10;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_uint32_to_usize(uint32_t);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__4;
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__13;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_resultIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_new(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(uint8_t, uint8_t);
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__6;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Expr_ReplaceImpl_Cache_hasResultFor(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__5;
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__11;
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_resultIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_keyIdx___boxed(lean_object*, lean_object*);
static size_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__9;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___closed__12;
static size_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Expr_ReplaceImpl_Cache_new___closed__3;
static size_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 13;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__3() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 2;
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__2;
x_3 = lean_usize_mul(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__3;
x_2 = lean_usize_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__4;
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__5;
x_3 = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_usize(x_3, 1, x_1);
return x_3;
}
}
static uint8_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__7() {
_start:
{
size_t x_1; size_t x_2; uint8_t x_3; 
x_1 = 1;
x_2 = 13;
x_3 = lean_usize_dec_le(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__8() {
_start:
{
size_t x_1; size_t x_2; 
x_1 = 1;
x_2 = lean_usize_shift_left(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__9() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__8;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__10() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 2;
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__9;
x_3 = lean_usize_mul(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__10;
x_2 = lean_usize_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__11;
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__13() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__9;
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__12;
x_3 = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_usize(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__14() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__7;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__6;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__13;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_new(lean_object* x_1) {
_start:
{
size_t x_2; uint32_t x_3; size_t x_4; uint8_t x_5; 
x_2 = 1;
x_3 = l_Lean_Expr_approxDepth(x_1);
x_4 = lean_uint32_to_usize(x_3);
x_5 = lean_usize_dec_le(x_4, x_2);
if (x_5 == 0)
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 13;
x_7 = 2;
x_8 = lean_usize_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__6;
return x_9;
}
else
{
size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_usize_shift_left(x_2, x_4);
x_11 = lean_usize_sub(x_10, x_2);
x_12 = lean_usize_mul(x_7, x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_usize(x_16, 1, x_11);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Expr_ReplaceImpl_Cache_new___closed__14;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ReplaceImpl_Cache_new(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_keyIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; 
x_3 = lean_ptr_addr(x_2);
x_4 = lean_ctor_get_usize(x_1, 1);
x_5 = lean_usize_mod(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_keyIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_keyIdx(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_resultIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; 
x_3 = lean_ptr_addr(x_2);
x_4 = lean_ctor_get_usize(x_1, 1);
x_5 = lean_usize_mod(x_3, x_4);
x_6 = lean_usize_add(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_resultIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_resultIdx(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_ReplaceImpl_Cache_hasResultFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_ctor_get_usize(x_1, 1);
x_6 = lean_usize_mod(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_9 = lean_usize_dec_eq(x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_hasResultFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_hasResultFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_ctor_get_usize(x_1, 1);
x_6 = lean_usize_mod(x_4, x_5);
x_7 = lean_usize_add(x_6, x_5);
x_8 = lean_array_uget(x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_getResultFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
size_t x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get_usize(x_1, 1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_mod(x_7, x_5);
x_9 = lean_array_uset(x_6, x_8, x_2);
x_10 = lean_usize_add(x_8, x_5);
x_11 = lean_array_uset(x_9, x_10, x_3);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get_usize(x_1, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ptr_addr(x_2);
x_15 = lean_usize_mod(x_14, x_12);
x_16 = lean_array_uset(x_13, x_15, x_2);
x_17 = lean_usize_add(x_15, x_12);
x_18 = lean_array_uset(x_16, x_17, x_3);
x_19 = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_usize(x_19, 1, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
x_4 = l_Lean_Expr_ReplaceImpl_Cache_store(x_3, x_1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_ctor_get_usize(x_3, 1);
x_7 = lean_usize_mod(x_5, x_6);
x_8 = lean_array_uget(x_4, x_7);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = lean_usize_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_12, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_13);
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_13, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_22 = lean_ptr_addr(x_15);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_24 = l_Lean_Expr_app___override(x_15, x_19);
lean_inc(x_24);
x_25 = l_Lean_Expr_ReplaceImpl_Cache_store(x_20, x_2, x_24);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_27 = lean_ptr_addr(x_19);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_app___override(x_15, x_19);
lean_inc(x_29);
x_30 = l_Lean_Expr_ReplaceImpl_Cache_store(x_20, x_2, x_29);
lean_ctor_set(x_17, 1, x_30);
lean_ctor_set(x_17, 0, x_29);
return x_17;
}
else
{
lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_15);
lean_inc_n(x_2, 2);
x_31 = l_Lean_Expr_ReplaceImpl_Cache_store(x_20, x_2, x_2);
lean_ctor_set(x_17, 1, x_31);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_35 = lean_ptr_addr(x_15);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
x_37 = l_Lean_Expr_app___override(x_15, x_32);
lean_inc(x_37);
x_38 = l_Lean_Expr_ReplaceImpl_Cache_store(x_33, x_2, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_41 = lean_ptr_addr(x_32);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l_Lean_Expr_app___override(x_15, x_32);
lean_inc(x_43);
x_44 = l_Lean_Expr_ReplaceImpl_Cache_store(x_33, x_2, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_32);
lean_dec(x_15);
lean_inc_n(x_2, 2);
x_46 = l_Lean_Expr_ReplaceImpl_Cache_store(x_33, x_2, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_49);
lean_inc(x_1);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_49, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_50, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_59 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_60 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_61 = lean_ptr_addr(x_53);
x_62 = lean_usize_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_50);
x_63 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_63);
x_64 = l_Lean_Expr_ReplaceImpl_Cache_store(x_58, x_2, x_63);
lean_ctor_set(x_55, 1, x_64);
lean_ctor_set(x_55, 0, x_63);
return x_55;
}
else
{
size_t x_65; size_t x_66; uint8_t x_67; 
x_65 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_66 = lean_ptr_addr(x_57);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
x_68 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_68);
x_69 = l_Lean_Expr_ReplaceImpl_Cache_store(x_58, x_2, x_68);
lean_ctor_set(x_55, 1, x_69);
lean_ctor_set(x_55, 0, x_68);
return x_55;
}
else
{
uint8_t x_70; 
x_70 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_51, x_51);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
x_71 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_71);
x_72 = l_Lean_Expr_ReplaceImpl_Cache_store(x_58, x_2, x_71);
lean_ctor_set(x_55, 1, x_72);
lean_ctor_set(x_55, 0, x_71);
return x_55;
}
else
{
lean_object* x_73; 
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_59);
x_73 = l_Lean_Expr_ReplaceImpl_Cache_store(x_58, x_2, x_59);
lean_ctor_set(x_55, 1, x_73);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_55, 0);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_55);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_76 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_77 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_78 = lean_ptr_addr(x_53);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_76);
lean_dec(x_50);
x_80 = l_Lean_Expr_lam___override(x_48, x_53, x_74, x_51);
lean_inc(x_80);
x_81 = l_Lean_Expr_ReplaceImpl_Cache_store(x_75, x_2, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
size_t x_83; size_t x_84; uint8_t x_85; 
x_83 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_84 = lean_ptr_addr(x_74);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_76);
x_86 = l_Lean_Expr_lam___override(x_48, x_53, x_74, x_51);
lean_inc(x_86);
x_87 = l_Lean_Expr_ReplaceImpl_Cache_store(x_75, x_2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_51, x_51);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
x_90 = l_Lean_Expr_lam___override(x_48, x_53, x_74, x_51);
lean_inc(x_90);
x_91 = l_Lean_Expr_ReplaceImpl_Cache_store(x_75, x_2, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_74);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_76);
x_93 = l_Lean_Expr_ReplaceImpl_Cache_store(x_75, x_2, x_76);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_ctor_get(x_2, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 2);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_96);
lean_inc(x_1);
x_99 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_96, x_3);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_97);
x_102 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_97, x_101);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
x_106 = l_Lean_Expr_forallE___override(x_95, x_96, x_97, x_98);
x_107 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_108 = lean_ptr_addr(x_100);
x_109 = lean_usize_dec_eq(x_107, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_106);
lean_dec(x_97);
x_110 = l_Lean_Expr_forallE___override(x_95, x_100, x_104, x_98);
lean_inc(x_110);
x_111 = l_Lean_Expr_ReplaceImpl_Cache_store(x_105, x_2, x_110);
lean_ctor_set(x_102, 1, x_111);
lean_ctor_set(x_102, 0, x_110);
return x_102;
}
else
{
size_t x_112; size_t x_113; uint8_t x_114; 
x_112 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_113 = lean_ptr_addr(x_104);
x_114 = lean_usize_dec_eq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_106);
x_115 = l_Lean_Expr_forallE___override(x_95, x_100, x_104, x_98);
lean_inc(x_115);
x_116 = l_Lean_Expr_ReplaceImpl_Cache_store(x_105, x_2, x_115);
lean_ctor_set(x_102, 1, x_116);
lean_ctor_set(x_102, 0, x_115);
return x_102;
}
else
{
uint8_t x_117; 
x_117 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_98, x_98);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_106);
x_118 = l_Lean_Expr_forallE___override(x_95, x_100, x_104, x_98);
lean_inc(x_118);
x_119 = l_Lean_Expr_ReplaceImpl_Cache_store(x_105, x_2, x_118);
lean_ctor_set(x_102, 1, x_119);
lean_ctor_set(x_102, 0, x_118);
return x_102;
}
else
{
lean_object* x_120; 
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_95);
lean_inc(x_106);
x_120 = l_Lean_Expr_ReplaceImpl_Cache_store(x_105, x_2, x_106);
lean_ctor_set(x_102, 1, x_120);
lean_ctor_set(x_102, 0, x_106);
return x_102;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; size_t x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_102, 0);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_102);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
x_123 = l_Lean_Expr_forallE___override(x_95, x_96, x_97, x_98);
x_124 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_125 = lean_ptr_addr(x_100);
x_126 = lean_usize_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_123);
lean_dec(x_97);
x_127 = l_Lean_Expr_forallE___override(x_95, x_100, x_121, x_98);
lean_inc(x_127);
x_128 = l_Lean_Expr_ReplaceImpl_Cache_store(x_122, x_2, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
size_t x_130; size_t x_131; uint8_t x_132; 
x_130 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_131 = lean_ptr_addr(x_121);
x_132 = lean_usize_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_123);
x_133 = l_Lean_Expr_forallE___override(x_95, x_100, x_121, x_98);
lean_inc(x_133);
x_134 = l_Lean_Expr_ReplaceImpl_Cache_store(x_122, x_2, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
else
{
uint8_t x_136; 
x_136 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_98, x_98);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_123);
x_137 = l_Lean_Expr_forallE___override(x_95, x_100, x_121, x_98);
lean_inc(x_137);
x_138 = l_Lean_Expr_ReplaceImpl_Cache_store(x_122, x_2, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_121);
lean_dec(x_100);
lean_dec(x_95);
lean_inc(x_123);
x_140 = l_Lean_Expr_ReplaceImpl_Cache_store(x_122, x_2, x_123);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_123);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
}
case 8:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_142 = lean_ctor_get(x_2, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_2, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_2, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_2, 3);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_143);
lean_inc(x_1);
x_147 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_143, x_3);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_144);
lean_inc(x_1);
x_150 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_144, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_145);
x_153 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_145, x_152);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; size_t x_157; size_t x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
x_157 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_158 = lean_ptr_addr(x_148);
x_159 = lean_usize_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_145);
lean_dec(x_144);
x_160 = l_Lean_Expr_letE___override(x_142, x_148, x_151, x_155, x_146);
lean_inc(x_160);
x_161 = l_Lean_Expr_ReplaceImpl_Cache_store(x_156, x_2, x_160);
lean_ctor_set(x_153, 1, x_161);
lean_ctor_set(x_153, 0, x_160);
return x_153;
}
else
{
size_t x_162; size_t x_163; uint8_t x_164; 
x_162 = lean_ptr_addr(x_144);
lean_dec(x_144);
x_163 = lean_ptr_addr(x_151);
x_164 = lean_usize_dec_eq(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_145);
x_165 = l_Lean_Expr_letE___override(x_142, x_148, x_151, x_155, x_146);
lean_inc(x_165);
x_166 = l_Lean_Expr_ReplaceImpl_Cache_store(x_156, x_2, x_165);
lean_ctor_set(x_153, 1, x_166);
lean_ctor_set(x_153, 0, x_165);
return x_153;
}
else
{
size_t x_167; size_t x_168; uint8_t x_169; 
x_167 = lean_ptr_addr(x_145);
lean_dec(x_145);
x_168 = lean_ptr_addr(x_155);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Lean_Expr_letE___override(x_142, x_148, x_151, x_155, x_146);
lean_inc(x_170);
x_171 = l_Lean_Expr_ReplaceImpl_Cache_store(x_156, x_2, x_170);
lean_ctor_set(x_153, 1, x_171);
lean_ctor_set(x_153, 0, x_170);
return x_153;
}
else
{
lean_object* x_172; 
lean_dec(x_155);
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_142);
lean_inc_n(x_2, 2);
x_172 = l_Lean_Expr_ReplaceImpl_Cache_store(x_156, x_2, x_2);
lean_ctor_set(x_153, 1, x_172);
lean_ctor_set(x_153, 0, x_2);
return x_153;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; size_t x_175; size_t x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_153, 0);
x_174 = lean_ctor_get(x_153, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_153);
x_175 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_176 = lean_ptr_addr(x_148);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_145);
lean_dec(x_144);
x_178 = l_Lean_Expr_letE___override(x_142, x_148, x_151, x_173, x_146);
lean_inc(x_178);
x_179 = l_Lean_Expr_ReplaceImpl_Cache_store(x_174, x_2, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_144);
lean_dec(x_144);
x_182 = lean_ptr_addr(x_151);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_145);
x_184 = l_Lean_Expr_letE___override(x_142, x_148, x_151, x_173, x_146);
lean_inc(x_184);
x_185 = l_Lean_Expr_ReplaceImpl_Cache_store(x_174, x_2, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
size_t x_187; size_t x_188; uint8_t x_189; 
x_187 = lean_ptr_addr(x_145);
lean_dec(x_145);
x_188 = lean_ptr_addr(x_173);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lean_Expr_letE___override(x_142, x_148, x_151, x_173, x_146);
lean_inc(x_190);
x_191 = l_Lean_Expr_ReplaceImpl_Cache_store(x_174, x_2, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_173);
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_142);
lean_inc_n(x_2, 2);
x_193 = l_Lean_Expr_ReplaceImpl_Cache_store(x_174, x_2, x_2);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_2);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
}
case 10:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_ctor_get(x_2, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_2, 1);
lean_inc(x_196);
lean_inc(x_196);
x_197 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_196, x_3);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; size_t x_201; size_t x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
x_201 = lean_ptr_addr(x_196);
lean_dec(x_196);
x_202 = lean_ptr_addr(x_199);
x_203 = lean_usize_dec_eq(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_Expr_mdata___override(x_195, x_199);
lean_inc(x_204);
x_205 = l_Lean_Expr_ReplaceImpl_Cache_store(x_200, x_2, x_204);
lean_ctor_set(x_197, 1, x_205);
lean_ctor_set(x_197, 0, x_204);
return x_197;
}
else
{
lean_object* x_206; 
lean_dec(x_199);
lean_dec(x_195);
lean_inc_n(x_2, 2);
x_206 = l_Lean_Expr_ReplaceImpl_Cache_store(x_200, x_2, x_2);
lean_ctor_set(x_197, 1, x_206);
lean_ctor_set(x_197, 0, x_2);
return x_197;
}
}
else
{
lean_object* x_207; lean_object* x_208; size_t x_209; size_t x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_197, 0);
x_208 = lean_ctor_get(x_197, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_197);
x_209 = lean_ptr_addr(x_196);
lean_dec(x_196);
x_210 = lean_ptr_addr(x_207);
x_211 = lean_usize_dec_eq(x_209, x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = l_Lean_Expr_mdata___override(x_195, x_207);
lean_inc(x_212);
x_213 = l_Lean_Expr_ReplaceImpl_Cache_store(x_208, x_2, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_207);
lean_dec(x_195);
lean_inc_n(x_2, 2);
x_215 = l_Lean_Expr_ReplaceImpl_Cache_store(x_208, x_2, x_2);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_2);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
case 11:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_2, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_2, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_2, 2);
lean_inc(x_219);
lean_inc(x_219);
x_220 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_219, x_3);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; size_t x_224; size_t x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_ctor_get(x_220, 1);
x_224 = lean_ptr_addr(x_219);
lean_dec(x_219);
x_225 = lean_ptr_addr(x_222);
x_226 = lean_usize_dec_eq(x_224, x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = l_Lean_Expr_proj___override(x_217, x_218, x_222);
lean_inc(x_227);
x_228 = l_Lean_Expr_ReplaceImpl_Cache_store(x_223, x_2, x_227);
lean_ctor_set(x_220, 1, x_228);
lean_ctor_set(x_220, 0, x_227);
return x_220;
}
else
{
lean_object* x_229; 
lean_dec(x_222);
lean_dec(x_218);
lean_dec(x_217);
lean_inc_n(x_2, 2);
x_229 = l_Lean_Expr_ReplaceImpl_Cache_store(x_223, x_2, x_2);
lean_ctor_set(x_220, 1, x_229);
lean_ctor_set(x_220, 0, x_2);
return x_220;
}
}
else
{
lean_object* x_230; lean_object* x_231; size_t x_232; size_t x_233; uint8_t x_234; 
x_230 = lean_ctor_get(x_220, 0);
x_231 = lean_ctor_get(x_220, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_220);
x_232 = lean_ptr_addr(x_219);
lean_dec(x_219);
x_233 = lean_ptr_addr(x_230);
x_234 = lean_usize_dec_eq(x_232, x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = l_Lean_Expr_proj___override(x_217, x_218, x_230);
lean_inc(x_235);
x_236 = l_Lean_Expr_ReplaceImpl_Cache_store(x_231, x_2, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_230);
lean_dec(x_218);
lean_dec(x_217);
lean_inc_n(x_2, 2);
x_238 = l_Lean_Expr_ReplaceImpl_Cache_store(x_231, x_2, x_2);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_2);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
default: 
{
lean_object* x_240; 
lean_dec(x_1);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_2);
lean_ctor_set(x_240, 1, x_3);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_1);
x_241 = lean_ctor_get(x_11, 0);
lean_inc(x_241);
lean_dec(x_11);
lean_inc(x_241);
x_242 = l_Lean_Expr_ReplaceImpl_Cache_store(x_3, x_2, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
else
{
size_t x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_2);
lean_dec(x_1);
x_244 = lean_usize_add(x_7, x_6);
x_245 = lean_array_uget(x_4, x_244);
lean_dec(x_4);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_3);
return x_246;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_new(x_2);
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
lean_inc(x_5);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_8 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = l_Lean_Expr_app___override(x_6, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_13 = lean_ptr_addr(x_7);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l_Lean_Expr_app___override(x_6, x_7);
return x_15;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_17);
lean_inc(x_1);
x_20 = l_Lean_Expr_replaceNoCache(x_1, x_17);
lean_inc(x_18);
x_21 = l_Lean_Expr_replaceNoCache(x_1, x_18);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_22 = l_Lean_Expr_lam___override(x_16, x_17, x_18, x_19);
x_23 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_24 = lean_ptr_addr(x_20);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_18);
x_26 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_26;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_28 = lean_ptr_addr(x_21);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
x_30 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_19, x_19);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
x_32 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_32;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
return x_22;
}
}
}
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_34);
lean_inc(x_1);
x_37 = l_Lean_Expr_replaceNoCache(x_1, x_34);
lean_inc(x_35);
x_38 = l_Lean_Expr_replaceNoCache(x_1, x_35);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_39 = l_Lean_Expr_forallE___override(x_33, x_34, x_35, x_36);
x_40 = lean_ptr_addr(x_34);
lean_dec(x_34);
x_41 = lean_ptr_addr(x_37);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_35);
x_43 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_43;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_45 = lean_ptr_addr(x_38);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
x_47 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_36, x_36);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_39);
x_49 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_49;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
return x_39;
}
}
}
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; uint8_t x_60; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_51);
lean_inc(x_1);
x_55 = l_Lean_Expr_replaceNoCache(x_1, x_51);
lean_inc(x_52);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceNoCache(x_1, x_52);
lean_inc(x_53);
x_57 = l_Lean_Expr_replaceNoCache(x_1, x_53);
x_58 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_59 = lean_ptr_addr(x_55);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_2);
x_61 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_61;
}
else
{
size_t x_62; size_t x_63; uint8_t x_64; 
x_62 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_63 = lean_ptr_addr(x_56);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_53);
lean_dec(x_2);
x_65 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_65;
}
else
{
size_t x_66; size_t x_67; uint8_t x_68; 
x_66 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_67 = lean_ptr_addr(x_57);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_69;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_50);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_inc(x_71);
x_72 = l_Lean_Expr_replaceNoCache(x_1, x_71);
x_73 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_74 = lean_ptr_addr(x_72);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = l_Lean_Expr_mdata___override(x_70, x_72);
return x_76;
}
else
{
lean_dec(x_72);
lean_dec(x_70);
return x_2;
}
}
case 11:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; uint8_t x_83; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
lean_inc(x_79);
x_80 = l_Lean_Expr_replaceNoCache(x_1, x_79);
x_81 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_82 = lean_ptr_addr(x_80);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_2);
x_84 = l_Lean_Expr_proj___override(x_77, x_78, x_80);
return x_84;
}
else
{
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
return x_2;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
lean_dec(x_3);
return x_85;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__1 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__1();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__2 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__2();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__3 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__3();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__4 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__4);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__5 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__5();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__5);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__6 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__6();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__6);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__7 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__7();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__8 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__8();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__9 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__9();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__10 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__10();
l_Lean_Expr_ReplaceImpl_Cache_new___closed__11 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__11();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__11);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__12 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__12();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__12);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__13 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__13();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__13);
l_Lean_Expr_ReplaceImpl_Cache_new___closed__14 = _init_l_Lean_Expr_ReplaceImpl_Cache_new___closed__14();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
