// Lean compiler output
// Module: Lean.Util.FindLevelMVar
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
lean_object* l_Lean_FindLevelMVar_mainLevel_match__1(lean_object*);
lean_object* l_List_foldr___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_Lean_FindLevelMVar_mainLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_main(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_FindLevelMVar_main___closed__1;
lean_object* l_Lean_FindLevelMVar_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_main_match__1(lean_object*);
lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_main_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
lean_object* l_Lean_FindLevelMVar_visitLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_mainLevel_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_main_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_2(x_2, x_11, x_13);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_3, x_15, x_16, x_18);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_7, x_20, x_21, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_4(x_5, x_25, x_26, x_27, x_29);
return x_30;
}
case 7:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_35 = lean_box_uint64(x_34);
x_36 = lean_apply_4(x_4, x_31, x_32, x_33, x_35);
return x_36;
}
case 8:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_5(x_6, x_37, x_38, x_39, x_40, x_42);
return x_43;
}
case 10:
{
lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_3(x_8, x_44, x_45, x_47);
return x_48;
}
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_53 = lean_box_uint64(x_52);
x_54 = lean_apply_4(x_9, x_49, x_50, x_51, x_53);
return x_54;
}
default: 
{
lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_apply_1(x_10, x_1);
return x_55;
}
}
}
}
lean_object* l_Lean_FindLevelMVar_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_FindLevelMVar_main_match__1___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_FindLevelMVar_mainLevel_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_2(x_3, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_4, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_5, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_2(x_6, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_2(x_7, x_29, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_FindLevelMVar_mainLevel_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_FindLevelMVar_mainLevel_match__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_FindLevelMVar_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Level_hasMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_FindLevelMVar_mainLevel(x_1, x_2, x_3);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_FindLevelMVar_mainLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_FindLevelMVar_visitLevel(x_1, x_4, x_3);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = l_Lean_FindLevelMVar_visitLevel(x_1, x_7, x_3);
x_9 = l_Lean_FindLevelMVar_visitLevel(x_1, x_6, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_FindLevelMVar_visitLevel(x_1, x_11, x_3);
x_13 = l_Lean_FindLevelMVar_visitLevel(x_1, x_10, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_14);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_FindLevelMVar_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_FindLevelMVar_main(x_1, x_2, x_3);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_FindLevelMVar_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_3, x_4);
x_6 = l_Lean_FindLevelMVar_visitLevel(x_1, x_2, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_FindLevelMVar_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_FindLevelMVar_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_FindLevelMVar_visitLevel(x_1, x_4, x_3);
return x_5;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_FindLevelMVar_main___lambda__1), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_FindLevelMVar_main___closed__1;
x_9 = l_List_foldr___rarg(x_7, x_8, x_6);
x_10 = lean_apply_1(x_9, x_3);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_FindLevelMVar_visit(x_1, x_11, x_3);
x_14 = l_Lean_FindLevelMVar_visit(x_1, x_12, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
x_17 = l_Lean_FindLevelMVar_visit(x_1, x_15, x_3);
x_18 = l_Lean_FindLevelMVar_visit(x_1, x_16, x_17);
return x_18;
}
case 7:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_21 = l_Lean_FindLevelMVar_visit(x_1, x_19, x_3);
x_22 = l_Lean_FindLevelMVar_visit(x_1, x_20, x_21);
return x_22;
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_26 = l_Lean_FindLevelMVar_visit(x_1, x_23, x_3);
lean_inc(x_1);
x_27 = l_Lean_FindLevelMVar_visit(x_1, x_24, x_26);
x_28 = l_Lean_FindLevelMVar_visit(x_1, x_25, x_27);
return x_28;
}
case 10:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Lean_FindLevelMVar_visit(x_1, x_29, x_3);
return x_30;
}
case 11:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Lean_FindLevelMVar_visit(x_1, x_31, x_3);
return x_32;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindLevelMVar_main(x_2, x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_FindLevelMVar(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_FindLevelMVar_main___closed__1 = _init_l_Lean_FindLevelMVar_main___closed__1();
lean_mark_persistent(l_Lean_FindLevelMVar_main___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
