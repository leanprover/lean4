// Lean compiler output
// Module: Lean.Compiler.IR.Sorry
// Imports: Lean.Compiler.IR.CompilerM
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
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_visitFndBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_visitFndBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_IR_updateSorryDep___closed__0;
static lean_object* _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sorryAx", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
x_17 = lean_name_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_1);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_20 = l_Lean_IR_findDecl___redArg(x_1, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_1);
x_24 = x_2;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 4);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_1);
x_24 = x_2;
goto block_28;
}
else
{
lean_object* x_31; 
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_4 = x_31;
x_5 = x_2;
x_6 = x_22;
goto block_15;
}
}
else
{
lean_dec(x_29);
lean_dec(x_1);
x_24 = x_2;
goto block_28;
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_4 = x_32;
x_5 = x_2;
x_6 = x_3;
goto block_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
block_15:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
x_8 = lean_name_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(x_4, x_2, x_3);
return x_5;
}
case 7:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(x_6, x_2, x_3);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitExpr___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitExpr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_visitFndBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_IR_Sorry_visitFndBody(x_20, x_5, x_6, x_7);
x_8 = x_21;
goto block_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_IR_Sorry_visitFndBody(x_22, x_5, x_6, x_7);
x_8 = x_23;
goto block_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
block_17:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
x_5 = x_12;
x_7 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_Sorry_visitExpr___redArg(x_5, x_2, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_1 = x_6;
x_2 = x_11;
x_4 = x_10;
goto _start;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_IR_Sorry_visitFndBody(x_13, x_2, x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_1 = x_14;
x_2 = x_19;
x_4 = x_18;
goto _start;
}
}
case 10:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_21);
x_26 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_23, x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_21);
x_30 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_35 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_visitFndBody_spec__0(x_21, x_33, x_34, x_24, x_2, x_3, x_4);
lean_dec(x_21);
return x_35;
}
}
}
default: 
{
uint8_t x_36; 
x_36 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_36 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_dec(x_1);
x_1 = x_37;
goto _start;
}
case 1:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
lean_dec(x_1);
x_1 = x_39;
goto _start;
}
case 2:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
lean_dec(x_1);
x_1 = x_41;
goto _start;
}
case 3:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_dec(x_1);
x_1 = x_43;
goto _start;
}
case 4:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
case 5:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_1, 5);
lean_inc(x_47);
lean_dec(x_1);
x_1 = x_47;
goto _start;
}
case 6:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
lean_dec(x_1);
x_1 = x_49;
goto _start;
}
case 7:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
lean_dec(x_1);
x_1 = x_51;
goto _start;
}
case 8:
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_1 = x_53;
goto _start;
}
case 9:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_1 = x_55;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_58 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_visitFndBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_visitFndBody_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitFndBody(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_IR_Sorry_visitFndBody(x_6, x_2, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_box(0);
x_21 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_19, x_5, x_17);
x_22 = lean_box(1);
lean_ctor_set(x_13, 0, x_21);
x_23 = lean_unbox(x_22);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_23);
lean_ctor_set(x_10, 0, x_20);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_24, x_5, x_17);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_25);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_33 = x_13;
} else {
 lean_dec_ref(x_13);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
x_35 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_32, x_5, x_31);
x_36 = lean_box(1);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 1, 1);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
lean_ctor_set(x_10, 1, x_37);
lean_ctor_set(x_10, 0, x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec(x_10);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_42 = x_9;
} else {
 lean_dec_ref(x_9);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
x_47 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_44, x_5, x_43);
x_48 = lean_box(1);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 1, 1);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_unbox(x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_49);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_9, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_10, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_10, 0, x_57);
return x_9;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_dec(x_10);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_9, 0, x_60);
return x_9;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_dec(x_9);
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_63 = x_10;
} else {
 lean_dec_ref(x_10);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_4);
return x_72;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_IR_Sorry_visitDecl(x_9, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_5 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
x_5 = x_2;
x_6 = x_4;
goto block_10;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
x_5 = x_2;
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_box(0);
x_19 = 0;
x_20 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0(x_1, x_19, x_20, x_18, x_2, x_3, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_5 = x_23;
x_6 = x_25;
goto block_10;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_2 = x_23;
x_4 = x_26;
goto _start;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_1);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_dec(x_33);
x_5 = x_30;
x_6 = x_4;
goto block_10;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_33, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
x_5 = x_30;
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_box(0);
x_37 = 0;
x_38 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_39 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0(x_1, x_37, x_38, x_36, x_30, x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_5 = x_41;
x_6 = x_43;
goto block_10;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_2 = x_41;
x_4 = x_44;
goto _start;
}
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Sorry_collect_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_collect(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_19, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_9 = x_6;
goto block_14;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_6, 4);
lean_dec(x_22);
x_23 = lean_ctor_get(x_6, 3);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
lean_ctor_set(x_6, 4, x_20);
x_9 = x_6;
goto block_14;
}
else
{
lean_object* x_27; 
lean_dec(x_6);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_20);
x_9 = x_27;
goto block_14;
}
}
}
else
{
x_9 = x_6;
goto block_14;
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_IR_updateSorryDep___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_IR_updateSorryDep___closed__0;
x_5 = l_Lean_IR_Sorry_collect(x_1, x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0(x_8, x_9, x_10, x_1);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_1);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0(x_14, x_15, x_16, x_1);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_updateSorryDep_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_updateSorryDep(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0 = _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0);
l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1 = _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1);
l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2 = _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2);
l_Lean_IR_updateSorryDep___closed__0 = _init_l_Lean_IR_updateSorryDep___closed__0();
lean_mark_persistent(l_Lean_IR_updateSorryDep___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
