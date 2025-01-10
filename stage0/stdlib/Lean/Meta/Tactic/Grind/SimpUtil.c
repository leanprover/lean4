// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.DoNotSimp
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__8;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__6;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__1;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__5;
lean_object* l_Lean_Meta_Grind_addDoNotSimp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__4;
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__3;
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindNormSimprocExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__2;
extern lean_object* l_Lean_Meta_Grind_grindNormExt;
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimprocs___rarg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__1;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__2;
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormSimprocExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_Grind_getSimprocs___rarg___closed__1;
x_5 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_4, x_1, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Meta_Grind_addDoNotSimp(x_7, x_1, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Simp_getSEvalSimprocs___rarg(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(0);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_array_mk(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_box(0);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_array_mk(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_5);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = l_Lean_Meta_Grind_addDoNotSimp(x_28, x_1, x_2, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Simp_getSEvalSimprocs___rarg(x_2, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_mk(x_39);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_44 = x_30;
} else {
 lean_dec_ref(x_30);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getSimprocs___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_getSimprocs___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_getSimprocs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_Lean_Meta_Grind_getSimpContext___closed__1;
x_7 = l_Lean_Meta_SimpExtension_getTheorems(x_6, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_8);
x_15 = lean_array_mk(x_10);
x_16 = l_Lean_Meta_Grind_getSimpContext___closed__2;
x_17 = l_Lean_Meta_Simp_mkContext(x_16, x_15, x_12, x_1, x_2, x_3, x_4, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
x_23 = l_Lean_Meta_Grind_getSimpContext___closed__2;
x_24 = l_Lean_Meta_Simp_mkContext(x_23, x_22, x_18, x_1, x_2, x_3, x_4, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimpContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__5;
x_3 = l_Lean_Meta_Grind_normalizeImp___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__2;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__6;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__3;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_Grind_getSimpContext(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Grind_getSimprocs___rarg(x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Grind_normalizeImp___closed__8;
x_15 = l_Lean_Meta_simp(x_1, x_8, x_11, x_13, x_14, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_DoNotSimp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_DoNotSimp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_getSimprocs___rarg___closed__1 = _init_l_Lean_Meta_Grind_getSimprocs___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___rarg___closed__1);
l_Lean_Meta_Grind_getSimpContext___closed__1 = _init_l_Lean_Meta_Grind_getSimpContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__1);
l_Lean_Meta_Grind_getSimpContext___closed__2 = _init_l_Lean_Meta_Grind_getSimpContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__2);
l_Lean_Meta_Grind_normalizeImp___closed__1 = _init_l_Lean_Meta_Grind_normalizeImp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__1);
l_Lean_Meta_Grind_normalizeImp___closed__2 = _init_l_Lean_Meta_Grind_normalizeImp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__2);
l_Lean_Meta_Grind_normalizeImp___closed__3 = _init_l_Lean_Meta_Grind_normalizeImp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__3);
l_Lean_Meta_Grind_normalizeImp___closed__4 = _init_l_Lean_Meta_Grind_normalizeImp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__4);
l_Lean_Meta_Grind_normalizeImp___closed__5 = _init_l_Lean_Meta_Grind_normalizeImp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__5);
l_Lean_Meta_Grind_normalizeImp___closed__6 = _init_l_Lean_Meta_Grind_normalizeImp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__6);
l_Lean_Meta_Grind_normalizeImp___closed__7 = _init_l_Lean_Meta_Grind_normalizeImp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__7);
l_Lean_Meta_Grind_normalizeImp___closed__8 = _init_l_Lean_Meta_Grind_normalizeImp___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
