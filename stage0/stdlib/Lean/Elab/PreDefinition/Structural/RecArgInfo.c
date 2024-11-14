// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.RecArgInfo
// Imports: Lean.Meta.Basic Lean.Meta.ForEachExpr Lean.Elab.PreDefinition.Structural.IndGroupInfo
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
static lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1;
static lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21(lean_object*);
static lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__2;
x_3 = l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1;
x_4 = l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__3;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__4;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_nat_dec_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__2(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_8, x_5);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_7, x_14);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_add(x_8, x_19);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_1, 3);
x_24 = l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1(x_23, x_20);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_array_fget(x_2, x_8);
x_26 = lean_array_push(x_18, x_25);
lean_ctor_set(x_10, 1, x_26);
x_27 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_27;
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_2, x_8);
x_30 = lean_array_push(x_17, x_29);
lean_ctor_set(x_10, 0, x_30);
x_31 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_31;
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_20);
x_33 = lean_array_fget(x_2, x_8);
x_34 = lean_array_push(x_17, x_33);
lean_ctor_set(x_10, 0, x_34);
x_35 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_35;
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_nat_add(x_8, x_39);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_nat_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_1, 3);
x_44 = l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1(x_43, x_40);
lean_dec(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_array_fget(x_2, x_8);
x_46 = lean_array_push(x_38, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_48;
x_9 = lean_box(0);
x_10 = x_47;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_array_fget(x_2, x_8);
x_51 = lean_array_push(x_37, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
x_53 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_53;
x_9 = lean_box(0);
x_10 = x_52;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
x_55 = lean_array_fget(x_2, x_8);
x_56 = lean_array_push(x_37, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
x_58 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_58;
x_9 = lean_box(0);
x_10 = x_57;
goto _start;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2;
lean_inc(x_3);
x_8 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__3(x_1, x_2, x_6, x_4, x_3, x_5, x_3, x_4, lean_box(0), x_7);
lean_dec(x_3);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_1, 5);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_instInhabitedName;
x_9 = l_outOfBounds___rarg(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_4, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Structural_RecArgInfo_indName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1 = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__1);
l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__2 = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__2);
l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__3 = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__3);
l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__4 = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo___closed__4);
l_Lean_Elab_Structural_instInhabitedRecArgInfo = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo);
l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1 = _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1);
l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2 = _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
