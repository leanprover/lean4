// Lean compiler output
// Module: Init.Lean.TypeContext
// Imports: Init.Control.Reader Init.Lean.NameGenerator Init.Lean.Environment Init.Lean.LocalContext Init.Lean.Trace
#include "runtime/lean.h"
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
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeContext_1__getOptions(lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_tracer___closed__2;
uint8_t l_Lean_TypeContext_isLevelAssigned___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_isLevelAssigned(lean_object*);
lean_object* l_Lean_TypeContext_tracer(lean_object*, lean_object*);
uint8_t lean_level_has_mvar(lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__1___boxed(lean_object*);
uint8_t l_Lean_TypeContext_hasAssignedMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_hasAssignedMVar___main(lean_object*);
lean_object* l_Lean_TypeContext_hasAssignedMVar___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar(lean_object*);
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___closed__3;
lean_object* l_Lean_TypeContext_isLevelAssigned___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__1(lean_object*);
uint8_t l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___closed__2;
lean_object* l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_hasAssignedMVar(lean_object*);
lean_object* l_Lean_TypeContext_tracer___closed__4;
lean_object* l_Lean_TypeContext_hasAssignedMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1(lean_object*);
lean_object* l_Lean_TypeContext_isExprAssigned___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_tracer___closed__1;
lean_object* l_Lean_TCState_backtrackable___closed__1;
lean_object* l_Lean_TCState_backtrackable(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___rarg(lean_object*);
uint8_t l_Lean_TypeContext_hasAssignedLevelMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar___main(lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l_Lean_TypeContext_tracer___closed__3;
lean_object* l_Lean_TypeContext_isExprAssigned(lean_object*);
uint8_t l_Lean_TypeContext_isExprAssigned___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TypeContext_hasAssignedMVar___main___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_TCState_backtrackable___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
return x_10;
}
}
}
lean_object* _init_l_Lean_TCState_backtrackable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TCState_backtrackable___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TCState_backtrackable___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TCState_backtrackable___lambda__2), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TCState_backtrackable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TCState_backtrackable___closed__1;
x_2 = l_Lean_TCState_backtrackable___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_TCState_backtrackable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TCState_backtrackable___closed__3;
return x_3;
}
}
lean_object* l_Lean_TCState_backtrackable___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TCState_backtrackable___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_TypeContext_isLevelAssigned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_TypeContext_isLevelAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeContext_isLevelAssigned___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_TypeContext_isLevelAssigned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TypeContext_isLevelAssigned___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_TypeContext_isExprAssigned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_TypeContext_isExprAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeContext_isExprAssigned___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_TypeContext_isExprAssigned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TypeContext_isExprAssigned___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
x_5 = lean_level_has_mvar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
x_3 = x_4;
goto _start;
}
}
case 2:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_8);
x_10 = lean_level_has_mvar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_level_has_mvar(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_8);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_9);
x_15 = lean_level_has_mvar(x_9);
if (x_15 == 0)
{
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
lean_inc(x_18);
x_20 = lean_level_has_mvar(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_inc(x_19);
x_21 = lean_level_has_mvar(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
else
{
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_18);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_19);
x_25 = lean_level_has_mvar(x_19);
if (x_25 == 0)
{
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
else
{
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_27 = 1;
return x_27;
}
}
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_2(x_29, x_2, x_28);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_30);
x_32 = 1;
return x_32;
}
}
default: 
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = 0;
return x_33;
}
}
}
}
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_TypeContext_hasAssignedLevelMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeContext_hasAssignedLevelMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_TypeContext_hasAssignedLevelMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TypeContext_hasAssignedLevelMVar___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_3, x_6);
x_8 = l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_5);
if (x_8 == 0)
{
return x_7;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
uint8_t l_Lean_TypeContext_hasAssignedMVar___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
case 3:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_TypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = 0;
x_13 = l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_12, x_11);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_expr_has_expr_mvar(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_expr_has_level_mvar(x_14);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
x_18 = lean_expr_has_expr_mvar(x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_expr_has_level_mvar(x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_14);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_expr_has_expr_mvar(x_15);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_has_level_mvar(x_15);
if (x_25 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_28 = 1;
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_14);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_expr_has_expr_mvar(x_15);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_expr_has_level_mvar(x_15);
if (x_31 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_34 = 1;
return x_34;
}
}
}
case 6:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_expr_has_expr_mvar(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_expr_has_level_mvar(x_35);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_35);
x_39 = lean_expr_has_expr_mvar(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_expr_has_level_mvar(x_36);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_41 = 0;
return x_41;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_35);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = lean_expr_has_expr_mvar(x_36);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = lean_expr_has_level_mvar(x_36);
if (x_46 == 0)
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_49 = 1;
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_35);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = lean_expr_has_expr_mvar(x_36);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = lean_expr_has_level_mvar(x_36);
if (x_52 == 0)
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_55 = 1;
return x_55;
}
}
}
case 7:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_expr_has_expr_mvar(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_expr_has_level_mvar(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
x_60 = lean_expr_has_expr_mvar(x_57);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_expr_has_level_mvar(x_57);
if (x_61 == 0)
{
uint8_t x_62; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
return x_62;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_65; 
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_56);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = lean_expr_has_expr_mvar(x_57);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = lean_expr_has_level_mvar(x_57);
if (x_67 == 0)
{
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
return x_65;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_70 = 1;
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_56);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_expr_has_expr_mvar(x_57);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = lean_expr_has_level_mvar(x_57);
if (x_73 == 0)
{
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
return x_71;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_76 = 1;
return x_76;
}
}
}
case 8:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_101; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 3);
lean_inc(x_79);
lean_dec(x_3);
x_101 = lean_expr_has_expr_mvar(x_77);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_expr_has_level_mvar(x_77);
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_77);
x_103 = 0;
x_80 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
lean_inc(x_2);
lean_inc(x_1);
x_104 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_77);
if (x_104 == 0)
{
x_80 = x_104;
goto block_100;
}
else
{
uint8_t x_105; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_105 = 1;
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_inc(x_2);
lean_inc(x_1);
x_106 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_77);
if (x_106 == 0)
{
x_80 = x_106;
goto block_100;
}
else
{
uint8_t x_107; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_107 = 1;
return x_107;
}
}
block_100:
{
uint8_t x_81; 
x_81 = lean_expr_has_expr_mvar(x_78);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_expr_has_level_mvar(x_78);
if (x_82 == 0)
{
lean_dec(x_78);
if (x_80 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_expr_mvar(x_79);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_expr_has_level_mvar(x_79);
if (x_84 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_80;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_87 = 1;
return x_87;
}
}
else
{
uint8_t x_88; 
lean_inc(x_2);
lean_inc(x_1);
x_88 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_78);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_expr_has_expr_mvar(x_79);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = lean_expr_has_level_mvar(x_79);
if (x_90 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_88;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_93; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_93 = 1;
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_inc(x_2);
lean_inc(x_1);
x_94 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_78);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = lean_expr_has_expr_mvar(x_79);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_expr_has_level_mvar(x_79);
if (x_96 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_94;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_99 = 1;
return x_99;
}
}
}
}
case 10:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_3, 1);
lean_inc(x_108);
lean_dec(x_3);
x_109 = lean_expr_has_expr_mvar(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_expr_has_level_mvar(x_108);
if (x_110 == 0)
{
uint8_t x_111; 
lean_dec(x_108);
lean_dec(x_2);
lean_dec(x_1);
x_111 = 0;
return x_111;
}
else
{
x_3 = x_108;
goto _start;
}
}
else
{
x_3 = x_108;
goto _start;
}
}
case 11:
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_3, 2);
lean_inc(x_114);
lean_dec(x_3);
x_115 = lean_expr_has_expr_mvar(x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = lean_expr_has_level_mvar(x_114);
if (x_116 == 0)
{
uint8_t x_117; 
lean_dec(x_114);
lean_dec(x_2);
lean_dec(x_1);
x_117 = 0;
return x_117;
}
else
{
x_3 = x_114;
goto _start;
}
}
else
{
x_3 = x_114;
goto _start;
}
}
default: 
{
uint8_t x_120; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
return x_120;
}
}
}
}
lean_object* l_Lean_TypeContext_hasAssignedMVar___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeContext_hasAssignedMVar___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_List_foldr___main___at_Lean_TypeContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_TypeContext_hasAssignedMVar___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_TypeContext_hasAssignedMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_TypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeContext_hasAssignedMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeContext_hasAssignedMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_TypeContext_hasAssignedMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TypeContext_hasAssignedMVar___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeContext_1__getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_TypeContext_1__getOptions___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_2__getTraceState___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeContext_2__getTraceState(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_TypeContext_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 3, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_apply_1(x_1, x_12);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_13);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* _init_l_Lean_TypeContext_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_2__getTraceState___boxed), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_TypeContext_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeContext_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeContext_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeContext_tracer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_TypeContext_tracer___closed__2;
x_2 = l_Lean_TypeContext_tracer___closed__3;
x_3 = l_Lean_TypeContext_tracer___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeContext_tracer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeContext_tracer___closed__4;
return x_3;
}
}
lean_object* l_Lean_TypeContext_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeContext_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_LocalContext(lean_object*);
lean_object* initialize_Init_Lean_Trace(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeContext(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_LocalContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TCState_backtrackable___closed__1 = _init_l_Lean_TCState_backtrackable___closed__1();
lean_mark_persistent(l_Lean_TCState_backtrackable___closed__1);
l_Lean_TCState_backtrackable___closed__2 = _init_l_Lean_TCState_backtrackable___closed__2();
lean_mark_persistent(l_Lean_TCState_backtrackable___closed__2);
l_Lean_TCState_backtrackable___closed__3 = _init_l_Lean_TCState_backtrackable___closed__3();
lean_mark_persistent(l_Lean_TCState_backtrackable___closed__3);
l_Lean_TypeContext_tracer___closed__1 = _init_l_Lean_TypeContext_tracer___closed__1();
lean_mark_persistent(l_Lean_TypeContext_tracer___closed__1);
l_Lean_TypeContext_tracer___closed__2 = _init_l_Lean_TypeContext_tracer___closed__2();
lean_mark_persistent(l_Lean_TypeContext_tracer___closed__2);
l_Lean_TypeContext_tracer___closed__3 = _init_l_Lean_TypeContext_tracer___closed__3();
lean_mark_persistent(l_Lean_TypeContext_tracer___closed__3);
l_Lean_TypeContext_tracer___closed__4 = _init_l_Lean_TypeContext_tracer___closed__4();
lean_mark_persistent(l_Lean_TypeContext_tracer___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
