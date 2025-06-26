// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: Std.Sat.CNF.Basic Std.Sat.CNF.RelabelFin
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___closed__0;
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__3;
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__0;
static lean_object* l_Std_Sat_CNF_dimacs_go___closed__0;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_nat_dec_le(x_4, x_6);
lean_dec(x_4);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_nat_dec_le(x_4, x_14);
lean_dec(x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_8, x_11);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
static lean_object* _init_l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_29; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_29 = lean_nat_dec_le(x_15, x_16);
lean_dec(x_15);
if (x_29 == 0)
{
lean_dec(x_14);
x_18 = x_3;
goto block_28;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
lean_inc(x_16);
lean_ctor_set(x_3, 1, x_16);
x_18 = x_3;
goto block_28;
}
else
{
lean_object* x_33; 
lean_dec(x_3);
lean_inc(x_16);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_16);
x_18 = x_33;
goto block_28;
}
}
block_13:
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; 
x_9 = lean_string_append(x_1, x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_string_push(x_9, x_10);
x_1 = x_11;
x_2 = x_6;
x_3 = x_7;
goto _start;
}
block_28:
{
uint8_t x_19; 
x_19 = lean_unbox(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___closed__0;
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_16, x_21);
x_23 = l_Nat_reprFast(x_22);
x_24 = lean_string_append(x_20, x_23);
lean_dec(x_23);
x_7 = x_18;
x_8 = x_24;
goto block_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_16, x_25);
x_27 = l_Nat_reprFast(x_26);
x_7 = x_18;
x_8 = x_27;
goto block_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_10);
x_11 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(x_1, x_6, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 48;
x_15 = lean_string_push(x_12, x_14);
x_16 = 10;
x_17 = lean_string_push(x_15, x_16);
x_1 = x_17;
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_21, x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(x_1, x_19, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 48;
x_30 = lean_string_push(x_27, x_29);
x_31 = 10;
x_32 = lean_string_push(x_30, x_31);
x_1 = x_32;
x_2 = x_20;
x_3 = x_28;
goto _start;
}
}
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Sat_CNF_dimacs_go___closed__0;
x_4 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_CNF_dimacs_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("p cnf ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = l_Std_Sat_CNF_dimacs___closed__0;
x_3 = l_Std_Sat_CNF_dimacs_go(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Std_Sat_CNF_dimacs___closed__1;
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_11 = l_Nat_reprFast(x_10);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = l_Std_Sat_CNF_dimacs___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_reprFast(x_6);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Std_Sat_CNF_dimacs___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_5);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_dimacs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_RelabelFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___closed__0 = _init_l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___closed__0();
lean_mark_persistent(l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0___closed__0);
l_Std_Sat_CNF_dimacs_go___closed__0 = _init_l_Std_Sat_CNF_dimacs_go___closed__0();
lean_mark_persistent(l_Std_Sat_CNF_dimacs_go___closed__0);
l_Std_Sat_CNF_dimacs___closed__0 = _init_l_Std_Sat_CNF_dimacs___closed__0();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__0);
l_Std_Sat_CNF_dimacs___closed__1 = _init_l_Std_Sat_CNF_dimacs___closed__1();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__1);
l_Std_Sat_CNF_dimacs___closed__2 = _init_l_Std_Sat_CNF_dimacs___closed__2();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__2);
l_Std_Sat_CNF_dimacs___closed__3 = _init_l_Std_Sat_CNF_dimacs___closed__3();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
