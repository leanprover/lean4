// Lean compiler output
// Module: Std.Sat.AIG.Relabel
// Imports: Std.Sat.AIG.Basic Std.Sat.AIG.Lemmas
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
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__0;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__8;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__7;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__4;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__2;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__14;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__9;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__13;
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__5;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__6;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__12;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__11;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__3;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__10;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_Decl_relabel___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_Decl_relabel___redArg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_relabel___redArg___closed__1;
x_2 = l_Std_Sat_AIG_relabel___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Sat_AIG_relabel___redArg___closed__5;
x_2 = l_Std_Sat_AIG_relabel___redArg___closed__4;
x_3 = l_Std_Sat_AIG_relabel___redArg___closed__3;
x_4 = l_Std_Sat_AIG_relabel___redArg___closed__2;
x_5 = l_Std_Sat_AIG_relabel___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_relabel___redArg___closed__6;
x_2 = l_Std_Sat_AIG_relabel___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Std_Sat_AIG_relabel___redArg___closed__10;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Sat_AIG_relabel___redArg___closed__11;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Sat_AIG_relabel___redArg___closed__12;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_relabel___redArg___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabel___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Std_Sat_AIG_relabel___redArg___closed__9;
x_8 = lean_array_size(x_4);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___redArg(x_7, x_6, x_8, x_9, x_4);
x_11 = l_Std_Sat_AIG_relabel___redArg___closed__14;
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabel___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Std_Sat_AIG_relabel___redArg___closed__9;
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___redArg(x_14, x_13, x_15, x_16, x_12);
x_18 = l_Std_Sat_AIG_relabel___redArg___closed__14;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_relabel___redArg(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_relabel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Std_Sat_AIG_relabel___redArg(x_1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Std_Sat_AIG_relabel___redArg(x_1, x_8);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_10);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = l_Std_Sat_AIG_relabel___redArg(x_1, x_14);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 1, 1);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_Entrypoint_relabel___redArg(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_Entrypoint_relabel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Relabel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_relabel___redArg___closed__0 = _init_l_Std_Sat_AIG_relabel___redArg___closed__0();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__0);
l_Std_Sat_AIG_relabel___redArg___closed__1 = _init_l_Std_Sat_AIG_relabel___redArg___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__1);
l_Std_Sat_AIG_relabel___redArg___closed__2 = _init_l_Std_Sat_AIG_relabel___redArg___closed__2();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__2);
l_Std_Sat_AIG_relabel___redArg___closed__3 = _init_l_Std_Sat_AIG_relabel___redArg___closed__3();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__3);
l_Std_Sat_AIG_relabel___redArg___closed__4 = _init_l_Std_Sat_AIG_relabel___redArg___closed__4();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__4);
l_Std_Sat_AIG_relabel___redArg___closed__5 = _init_l_Std_Sat_AIG_relabel___redArg___closed__5();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__5);
l_Std_Sat_AIG_relabel___redArg___closed__6 = _init_l_Std_Sat_AIG_relabel___redArg___closed__6();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__6);
l_Std_Sat_AIG_relabel___redArg___closed__7 = _init_l_Std_Sat_AIG_relabel___redArg___closed__7();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__7);
l_Std_Sat_AIG_relabel___redArg___closed__8 = _init_l_Std_Sat_AIG_relabel___redArg___closed__8();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__8);
l_Std_Sat_AIG_relabel___redArg___closed__9 = _init_l_Std_Sat_AIG_relabel___redArg___closed__9();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__9);
l_Std_Sat_AIG_relabel___redArg___closed__10 = _init_l_Std_Sat_AIG_relabel___redArg___closed__10();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__10);
l_Std_Sat_AIG_relabel___redArg___closed__11 = _init_l_Std_Sat_AIG_relabel___redArg___closed__11();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__11);
l_Std_Sat_AIG_relabel___redArg___closed__12 = _init_l_Std_Sat_AIG_relabel___redArg___closed__12();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__12);
l_Std_Sat_AIG_relabel___redArg___closed__13 = _init_l_Std_Sat_AIG_relabel___redArg___closed__13();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__13);
l_Std_Sat_AIG_relabel___redArg___closed__14 = _init_l_Std_Sat_AIG_relabel___redArg___closed__14();
lean_mark_persistent(l_Std_Sat_AIG_relabel___redArg___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
