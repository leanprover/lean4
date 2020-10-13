// Lean compiler output
// Module: Lean.Util.SCC
// Imports: Init Std.Data.HashMap
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_SCC_scc(lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1;
lean_object* l___private_Lean_Util_SCC_6__addSCCAux(lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_SCC_scc___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_1__getDataOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg___lambda__1(lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux(lean_object*);
lean_object* l___private_Lean_Util_SCC_2__push(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1;
lean_object* l___private_Lean_Util_SCC_8__sccAux___main(lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_7__addSCC___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_2__push___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1(lean_object*);
lean_object* l___private_Lean_Util_SCC_7__addSCC(lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_4__resetOnStack(lean_object*);
lean_object* l_List_forM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_5__updateLowLinkOf___spec__1(lean_object*);
lean_object* l___private_Lean_Util_SCC_1__getDataOf(lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main(lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_5__updateLowLinkOf___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf(lean_object*);
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Util_SCC_1__getDataOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_5, x_3);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l___private_Lean_Util_SCC_1__getDataOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_1__getDataOf___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_2__push___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = 1;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_8, x_3, x_14);
lean_ctor_set(x_4, 2, x_15);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_ctor_get(x_4, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_19, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_26 = 1;
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
x_28 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_20, x_3, x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
lean_object* l___private_Lean_Util_SCC_2__push(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_2__push___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_1(x_4, x_11);
x_13 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_7, x_3, x_12);
lean_ctor_set(x_5, 2, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_18, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_apply_1(x_4, x_24);
x_26 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_18, x_3, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_3__modifyDataOf___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_1(x_4, x_11);
x_13 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_7, x_3, x_12);
lean_ctor_set(x_5, 2, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_18, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_apply_1(x_4, x_24);
x_26 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_18, x_3, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_6);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_4__resetOnStack___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1;
x_6 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Util_SCC_4__resetOnStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_4__resetOnStack___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_5__updateLowLinkOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_1(x_4, x_11);
x_13 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_7, x_3, x_12);
lean_ctor_set(x_5, 2, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_18, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_apply_1(x_4, x_24);
x_26 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_18, x_3, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_5__updateLowLinkOf___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_5__updateLowLinkOf___spec__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
return x_2;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_nat_dec_lt(x_16, x_18);
if (x_19 == 0)
{
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_dec(x_18);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_nat_dec_lt(x_16, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_2, 1, x_23);
return x_2;
}
}
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_28 = x_1;
} else {
 lean_dec_ref(x_1);
 x_28 = lean_box(0);
}
x_29 = lean_nat_dec_lt(x_26, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_26);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_25);
return x_33;
}
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_5__updateLowLinkOf___spec__1___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 3);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_6, 3, x_10);
lean_ctor_set(x_6, 0, x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1;
lean_inc(x_21);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1___rarg(x_1, x_2, x_21, x_23, x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_inc(x_21);
lean_ctor_set(x_4, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_28 = lean_apply_2(x_1, x_3, x_21);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_free_object(x_24);
{
lean_object* _tmp_3 = x_22;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_26;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_26, 3);
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_26, 3, x_34);
lean_ctor_set(x_26, 0, x_22);
x_35 = lean_box(0);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_26, 1);
x_37 = lean_ctor_get(x_26, 2);
x_38 = lean_ctor_get(x_26, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_box(0);
lean_ctor_set(x_24, 1, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
lean_inc(x_21);
lean_ctor_set(x_4, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_43 = lean_apply_2(x_1, x_3, x_21);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
{
lean_object* _tmp_3 = x_22;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_42;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 3);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 4, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_22);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
x_56 = l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1;
lean_inc(x_54);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Util_SCC_4__resetOnStack___spec__1___rarg(x_1, x_2, x_54, x_56, x_6);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
lean_inc(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_61 = lean_apply_2(x_1, x_3, x_54);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_dec(x_59);
x_4 = x_55;
x_5 = x_60;
x_6 = x_58;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 3);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_66);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 4, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_59;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_6__addSCCAux___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_SCC_6__addSCCAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Util_SCC_6__addSCCAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_6__addSCCAux___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_7__addSCC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Util_SCC_6__addSCCAux___main___rarg(x_1, x_2, x_3, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Util_SCC_7__addSCC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_7__addSCC___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Util_SCC_1__getDataOf___rarg(x_1, x_2, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Util_SCC_8__sccAux___main___rarg(x_1, x_2, x_3, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Util_SCC_1__getDataOf___rarg(x_1, x_2, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg(x_1, x_2, x_4, x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_3);
x_18 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_dec(x_8);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg(x_1, x_2, x_4, x_9, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_Monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Util_SCC_2__push___rarg(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_8__sccAux___main___rarg___lambda__1), 6, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_inc(x_4);
x_9 = lean_apply_1(x_3, x_4);
x_10 = l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1;
x_11 = l_List_forM___main___rarg(x_10, lean_box(0), x_8, x_9);
x_12 = lean_apply_1(x_11, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Util_SCC_1__getDataOf___rarg(x_1, x_2, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l___private_Lean_Util_SCC_7__addSCC___rarg(x_1, x_2, x_4, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_14, 1);
x_35 = lean_ctor_get(x_14, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_14, 0, x_39);
return x_14;
}
else
{
lean_object* x_40; 
lean_free_object(x_14);
x_40 = l___private_Lean_Util_SCC_7__addSCC___rarg(x_1, x_2, x_4, x_34);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_ctor_get(x_16, 0);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = l___private_Lean_Util_SCC_7__addSCC___rarg(x_1, x_2, x_4, x_41);
return x_47;
}
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_8__sccAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_8__sccAux___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_8__sccAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_SCC_8__sccAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Util_SCC_8__sccAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_8__sccAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_SCC_scc___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Util_SCC_1__getDataOf___rarg(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_Util_SCC_8__sccAux___main___rarg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
lean_object* l_Lean_SCC_scc___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_alloc_closure((void*)(l_Lean_SCC_scc___rarg___lambda__1), 5, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_HashMap_inhabited___closed__1;
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_6);
x_10 = l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1;
x_11 = l_List_forM___main___rarg(x_10, lean_box(0), x_5, x_3);
x_12 = lean_apply_1(x_11, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_List_reverse___rarg(x_14);
return x_15;
}
}
lean_object* l_Lean_SCC_scc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SCC_scc___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_Data_HashMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_SCC(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1 = _init_l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1);
l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1 = _init_l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1);
l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1 = _init_l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
