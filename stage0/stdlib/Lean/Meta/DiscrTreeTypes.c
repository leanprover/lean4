// Lean compiler output
// Module: Lean.Meta.DiscrTreeTypes
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
lean_object* l_Lean_Meta_DiscrTree_Key_hash_match__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_root___default(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_beq_match__1(lean_object*);
extern lean_object* l_Std_PersistentHashMap_root___default___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_beq___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2;
lean_object* l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3___closed__1;
lean_object* l_Lean_Meta_DiscrTree_Key_hash_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_root___default___closed__1;
uint8_t l_Lean_Literal_beq(lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_beq_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Literal_hash(lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3;
size_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__1;
static lean_object* _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(3);
return x_1;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_hash_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_3, x_10, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_6, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_hash_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_hash_match__1___rarg), 6, 0);
return x_2;
}
}
size_t l_Lean_Meta_DiscrTree_Key_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 5237;
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_mix_hash(x_5, x_6);
x_8 = lean_usize_mix_hash(x_4, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = 3541;
x_12 = l_Lean_Name_hash(x_9);
x_13 = lean_usize_of_nat(x_10);
x_14 = lean_usize_mix_hash(x_12, x_13);
x_15 = lean_usize_mix_hash(x_11, x_14);
return x_15;
}
case 2:
{
lean_object* x_16; size_t x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = 1879;
x_18 = l_Lean_Literal_hash(x_16);
x_19 = lean_usize_mix_hash(x_17, x_18);
return x_19;
}
case 3:
{
size_t x_20; 
x_20 = 7883;
return x_20;
}
default: 
{
size_t x_21; 
x_21 = 2411;
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_Key_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_beq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_4(x_3, x_9, x_10, x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_apply_2(x_8, x_1, x_2);
return x_14;
}
}
case 1:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_4(x_4, x_15, x_16, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_4);
x_20 = lean_apply_2(x_8, x_1, x_2);
return x_20;
}
}
case 2:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_2(x_5, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_5);
x_24 = lean_apply_2(x_8, x_1, x_2);
return x_24;
}
}
case 3:
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_6, x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_6);
x_27 = lean_apply_2(x_8, x_1, x_2);
return x_27;
}
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_7, x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_7);
x_30 = lean_apply_2(x_8, x_1, x_2);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_beq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_beq_match__1___rarg), 8, 0);
return x_2;
}
}
uint8_t l_Lean_Meta_DiscrTree_Key_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_name_eq(x_11, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_12, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_2, 0);
x_21 = l_Lean_Literal_beq(x_19, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
default: 
{
if (lean_obj_tag(x_2) == 4)
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_Key_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_root___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_root___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_root___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_root___default___closed__1;
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_DiscrTreeTypes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__1 = _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__1);
l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2___closed__1 = _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2___closed__1);
l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2 = _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__2);
l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3___closed__1 = _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3___closed__1);
l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3 = _init_l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Lean_Meta_DiscrTreeTypes___instance__3);
l_Lean_Meta_DiscrTree_root___default___closed__1 = _init_l_Lean_Meta_DiscrTree_root___default___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_root___default___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
