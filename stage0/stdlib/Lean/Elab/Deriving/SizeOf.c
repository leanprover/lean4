// Lean compiler output
// Module: Lean.Elab.Deriving.SizeOf
// Imports: Init Lean.Meta.SizeOf Lean.Elab.Deriving.Basic
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
lean_object* l_Lean_Meta_mkSizeOfInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__2;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__3;
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_environment_find(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 5)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_environment_find(x_19, x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 5)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_isInductive___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__1(x_8, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_6 = x_20;
goto _start;
}
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkSizeOfInstances(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_32; uint8_t x_33; 
x_5 = lean_array_get_size(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_5);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_6 = x_34;
x_7 = x_4;
goto block_31;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_5);
x_37 = l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__2(x_1, x_35, x_36, x_2, x_3, x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = 1;
x_6 = x_41;
x_7 = x_40;
goto block_31;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = 0;
x_6 = x_43;
x_7 = x_42;
goto block_31;
}
}
block_31:
{
if (x_6 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_5);
lean_dec(x_5);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_1, x_11);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lambda__1___boxed), 8, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_17, x_2, x_3, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInductive___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SizeOf", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__2;
x_3 = l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__3;
x_4 = l_Lean_Elab_registerDerivingHandler(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SizeOf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SizeOf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__1 = _init_l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__1);
l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__2 = _init_l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__2);
l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__3 = _init_l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80____closed__3);
if (builtin) {res = l_Lean_Elab_Deriving_SizeOf_initFn____x40_Lean_Elab_Deriving_SizeOf___hyg_80_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
