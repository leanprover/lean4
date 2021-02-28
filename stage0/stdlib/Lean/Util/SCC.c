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
lean_object* l_Lean_SCC_State_data___default___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(lean_object*);
lean_object* l_Lean_SCC_Data_index_x3f___default;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_State_data___default(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__1;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf_match__1(lean_object*);
lean_object* l_Lean_SCC_scc_match__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf_match__1(lean_object*);
uint8_t l_Lean_SCC_Data_onStack___default;
lean_object* l_Lean_SCC_State_stack___default(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_Data_lowlink_x3f___default;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add_match__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf_match__1(lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
lean_object* l_Lean_SCC_State_sccs___default(lean_object*);
lean_object* l_Lean_SCC_scc___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc_match__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__2;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SCC_State_nextIndex___default;
static lean_object* _init_l_Lean_SCC_Data_index_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_SCC_Data_lowlink_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_SCC_Data_onStack___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_Lean_SCC_State_stack___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_SCC_State_nextIndex___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
lean_object* l_Lean_SCC_State_data___default(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashMap_instInhabitedHashMap___closed__1;
return x_4;
}
}
lean_object* l_Lean_SCC_State_data___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SCC_State_data___default(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_SCC_State_sccs___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1() {
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
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
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
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_12);
x_13 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_6, x_3, x_10);
lean_ctor_set(x_4, 2, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_6, x_3, x_19);
lean_ctor_set(x_4, 2, x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Std_HashMapImp_find_x3f___rarg(x_1, x_2, x_25, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = 0;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 1);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_35);
x_37 = l_Std_HashMapImp_insert___rarg(x_1, x_2, x_25, x_3, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_26);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_1(x_4, x_2);
return x_7;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_2(x_5, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Std_HashMapImp_find_x3f___rarg(x_2, x_3, x_7, x_4);
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
lean_ctor_set(x_11, 1, x_1);
x_15 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_11);
lean_ctor_set(x_5, 2, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_20);
lean_ctor_set(x_5, 2, x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_11, 1);
lean_dec(x_25);
x_26 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_11);
lean_ctor_set(x_5, 2, x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_31);
lean_ctor_set(x_5, 2, x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_11, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
lean_dec(x_12);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_nat_dec_lt(x_37, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
lean_ctor_set(x_11, 1, x_1);
x_41 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_11);
lean_ctor_set(x_5, 2, x_41);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set(x_11, 1, x_1);
x_44 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_11);
lean_ctor_set(x_5, 2, x_44);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_nat_dec_lt(x_37, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_11, 1, x_49);
x_50 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_11);
lean_ctor_set(x_5, 2, x_50);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_11, 1, x_53);
x_54 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_11);
lean_ctor_set(x_5, 2, x_54);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_5);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
lean_inc(x_57);
lean_dec(x_11);
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_61 = x_1;
} else {
 lean_dec_ref(x_1);
 x_61 = lean_box(0);
}
x_62 = lean_nat_dec_lt(x_59, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_60);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_58);
x_65 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_64);
lean_ctor_set(x_5, 2, x_65);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_59);
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_58);
x_70 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_7, x_4, x_69);
lean_ctor_set(x_5, 2, x_70);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
return x_72;
}
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_5, 0);
x_74 = lean_ctor_get(x_5, 1);
x_75 = lean_ctor_get(x_5, 2);
x_76 = lean_ctor_get(x_5, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_77 = l_Std_HashMapImp_find_x3f___rarg(x_2, x_3, x_75, x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_76);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_81, sizeof(void*)*2);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 1);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_1);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_84);
x_87 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_75, x_4, x_86);
x_88 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_74);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_76);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_81, sizeof(void*)*2);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 1);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_82);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_92);
x_95 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_75, x_4, x_94);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_73);
lean_ctor_set(x_96, 1, x_74);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_76);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_81, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_81, sizeof(void*)*2);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_101 = x_81;
} else {
 lean_dec_ref(x_81);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_82, 0);
lean_inc(x_102);
lean_dec(x_82);
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_104 = x_1;
} else {
 lean_dec_ref(x_1);
 x_104 = lean_box(0);
}
x_105 = lean_nat_dec_lt(x_102, x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_102);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_103);
if (lean_is_scalar(x_101)) {
 x_107 = lean_alloc_ctor(0, 2, 1);
} else {
 x_107 = x_101;
}
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_100);
x_108 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_75, x_4, x_107);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_73);
lean_ctor_set(x_109, 1, x_74);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_76);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_103);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_104;
}
lean_ctor_set(x_112, 0, x_102);
if (lean_is_scalar(x_101)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_101;
}
lean_ctor_set(x_113, 0, x_99);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_100);
x_114 = l_Std_HashMapImp_insert___rarg(x_2, x_3, x_75, x_4, x_113);
x_115 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_115, 0, x_73);
lean_ctor_set(x_115, 1, x_74);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_76);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2___rarg(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add_match__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_6, 3, x_11);
lean_ctor_set(x_6, 0, x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2___rarg(x_1, x_2, x_22, x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_inc(x_22);
lean_ctor_set(x_4, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_28 = lean_apply_2(x_1, x_3, x_22);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_free_object(x_24);
{
lean_object* _tmp_3 = x_23;
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
lean_ctor_set(x_26, 0, x_23);
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
lean_ctor_set(x_40, 0, x_23);
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
lean_inc(x_22);
lean_ctor_set(x_4, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_43 = lean_apply_2(x_1, x_3, x_22);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
{
lean_object* _tmp_3 = x_23;
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
lean_ctor_set(x_51, 0, x_23);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
lean_inc(x_54);
lean_inc(x_2);
lean_inc(x_1);
x_56 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__2___rarg(x_1, x_2, x_54, x_6);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
lean_inc(x_54);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_60 = lean_apply_2(x_1, x_3, x_54);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_58);
x_4 = x_55;
x_5 = x_59;
x_6 = x_57;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 3);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_65);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 4, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_58;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg(x_1, x_2, x_3, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_5, x_6);
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
x_11 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(x_1, x_2, x_3, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2___rarg(x_16, x_1, x_2, x_4, x_15);
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
x_26 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__2___rarg(x_9, x_1, x_2, x_4, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___lambda__1), 6, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_inc(x_4);
x_9 = lean_apply_1(x_3, x_4);
x_10 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__2;
x_11 = l_List_forM___rarg(x_10, lean_box(0), x_8, x_9);
x_12 = lean_apply_1(x_11, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_4, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2;
x_21 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____rarg(x_20, x_18, x_19);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; 
lean_free_object(x_14);
x_24 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(x_1, x_2, x_4, x_17);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2;
x_30 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____rarg(x_29, x_27, x_28);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(x_1, x_2, x_4, x_26);
return x_34;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_SCC_scc_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_SCC_scc_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_SCC_scc_match__1___rarg), 2, 0);
return x_5;
}
}
lean_object* l_Lean_SCC_scc_match__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SCC_scc_match__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_SCC_scc___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_4, x_5);
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
x_10 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(x_1, x_2, x_3, x_4, x_9);
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
x_8 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_6);
x_10 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__2;
x_11 = l_List_forM___rarg(x_10, lean_box(0), x_5, x_3);
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
l_Lean_SCC_Data_index_x3f___default = _init_l_Lean_SCC_Data_index_x3f___default();
lean_mark_persistent(l_Lean_SCC_Data_index_x3f___default);
l_Lean_SCC_Data_lowlink_x3f___default = _init_l_Lean_SCC_Data_lowlink_x3f___default();
lean_mark_persistent(l_Lean_SCC_Data_lowlink_x3f___default);
l_Lean_SCC_Data_onStack___default = _init_l_Lean_SCC_Data_onStack___default();
l_Lean_SCC_State_nextIndex___default = _init_l_Lean_SCC_State_nextIndex___default();
lean_mark_persistent(l_Lean_SCC_State_nextIndex___default);
l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1);
l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__1);
l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
