// Lean compiler output
// Module: Std.Sat.AIG.CNF
// Imports: Std.Sat.CNF Std.Sat.AIG.Basic Std.Sat.AIG.Lemmas
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectLeftAssign___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectRightAssign___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_inj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_falseToCNF(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectRightAssign___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectLeftAssign___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atomToCNF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_mixAssigns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_mixAssigns___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_inj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_State_eval___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_mixAssigns___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_init(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_State_eval(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectLeftAssign(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectRightAssign(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_falseToCNF(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_Decl_falseToCNF___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_box(1);
lean_inc(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atomToCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_Decl_atomToCNF___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_29; 
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
if (x_4 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
x_29 = x_40;
goto block_38;
}
else
{
uint8_t x_41; 
x_41 = lean_unbox(x_6);
x_29 = x_41;
goto block_38;
}
block_28:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_box(x_10);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
block_38:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_box(x_29);
lean_inc(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
if (x_5 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(1);
x_36 = lean_unbox(x_35);
x_8 = x_34;
x_9 = x_32;
x_10 = x_36;
goto block_28;
}
else
{
uint8_t x_37; 
x_37 = lean_unbox(x_6);
x_8 = x_34;
x_9 = x_32;
x_10 = x_37;
goto block_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_Decl_gateToCNF___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Std_Sat_AIG_Decl_gateToCNF___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Std_Sat_AIG_Decl_gateToCNF(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_mixAssigns___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_mixAssigns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_Sat_AIG_toCNF_mixAssigns___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_mixAssigns___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_toCNF_mixAssigns___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Sat_AIG_toCNF_mixAssigns(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectLeftAssign___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_AIG_toCNF_projectLeftAssign___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectLeftAssign___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_AIG_toCNF_projectLeftAssign___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_toCNF_projectLeftAssign(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectRightAssign___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_projectRightAssign(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_Sat_AIG_toCNF_projectRightAssign___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectRightAssign___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_AIG_toCNF_projectRightAssign___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Sat_AIG_toCNF_projectRightAssign(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Std_Sat_AIG_denote_go___redArg(x_5, x_7, x_1);
if (x_8 == 0)
{
return x_6;
}
else
{
if (x_6 == 0)
{
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Std_Sat_AIG_denote___at___Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Std_Sat_AIG_toCNF_mixAssigns___redArg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_AIG_denote___at___Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_toCNF_cnfSatAssignment(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_init(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
x_4 = lean_box(0);
x_5 = lean_mk_array(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_toCNF_Cache_init(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = lean_array_fset(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg(x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toCNF_Cache_addFalse(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = lean_array_fset(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg(x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_toCNF_Cache_addAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(1);
x_6 = lean_array_fset(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Sat_AIG_toCNF_Cache_addGate___redArg(x_3, x_4, x_5, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_toCNF_Cache_addGate___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Sat_AIG_toCNF_Cache_addGate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Std_Sat_AIG_toCNF_Cache_init(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_toCNF_State_empty(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg(x_5, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Std_Sat_AIG_Decl_falseToCNF___redArg(x_7);
x_9 = l_List_appendTR___redArg(x_8, x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Std_Sat_AIG_toCNF_Cache_addFalse___redArg(x_11, x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_Std_Sat_AIG_Decl_falseToCNF___redArg(x_13);
x_15 = l_List_appendTR___redArg(x_14, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_toCNF_State_addFalse___redArg(x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_toCNF_State_addFalse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg(x_6, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Std_Sat_AIG_Decl_atomToCNF___redArg(x_8, x_9);
x_11 = l_List_appendTR___redArg(x_10, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_Std_Sat_AIG_toCNF_Cache_addAtom___redArg(x_13, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l_Std_Sat_AIG_Decl_atomToCNF___redArg(x_15, x_16);
x_18 = l_List_appendTR___redArg(x_17, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toCNF_State_addAtom___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toCNF_State_addAtom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_21; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
lean_inc(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_shiftr(x_1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_nat_shiftr(x_2, x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_30 = lean_nat_land(x_9, x_1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_21 = x_34;
goto block_29;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_21 = x_36;
goto block_29;
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Std_Sat_AIG_toCNF_Cache_addGate___redArg(x_1, x_2, x_6, x_4);
lean_dec(x_4);
x_17 = l_Std_Sat_AIG_Decl_gateToCNF___redArg(x_8, x_11, x_13, x_14, x_15);
x_18 = l_List_appendTR___redArg(x_17, x_5);
if (lean_is_scalar(x_7)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_7;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_nat_land(x_9, x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_14 = x_21;
x_15 = x_26;
goto block_20;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
x_14 = x_21;
x_15 = x_28;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_toCNF_State_addGate___redArg(x_2, x_3, x_4, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_toCNF_State_addGate___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_toCNF_State_addGate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Std_Sat_CNF_eval___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_toCNF_State_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_AIG_toCNF_State_eval___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_AIG_toCNF_State_eval___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_toCNF_State_eval(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_inj(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_inj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_toCNF_inj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_array_fget(x_4, x_2);
lean_dec(x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_array_fget(x_7, x_2);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_toCNF_State_addFalse___redArg(x_3, x_2);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_Sat_AIG_toCNF_State_addAtom___redArg(x_10, x_3, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_shiftr(x_12, x_14);
x_16 = l_Std_Sat_AIG_toCNF_go___redArg(x_1, x_15, x_3);
x_17 = lean_nat_shiftr(x_13, x_14);
x_18 = l_Std_Sat_AIG_toCNF_go___redArg(x_1, x_17, x_16);
x_19 = l_Std_Sat_AIG_toCNF_State_addGate___redArg(x_12, x_13, x_18, x_2);
lean_dec(x_13);
lean_dec(x_12);
return x_19;
}
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_toCNF_go___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_toCNF_go___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_toCNF_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_7 = l_Std_Sat_AIG_toCNF_State_empty(x_3);
lean_inc(x_5);
x_8 = l_Std_Sat_AIG_toCNF_go___redArg(x_3, x_5, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
if (x_6 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_10 = x_30;
goto block_28;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_10 = x_32;
goto block_28;
}
block_28:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = lean_box(x_10);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_9);
x_15 = lean_box(0);
if (lean_is_scalar(x_4)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_4;
 lean_ctor_set_tag(x_16, 1);
}
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toCNF_inj___boxed), 2, 1);
lean_closure_set(x_18, 0, x_3);
x_19 = l_Std_Sat_CNF_relabel___redArg(x_18, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_box(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(0);
if (lean_is_scalar(x_4)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_4;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toCNF_inj___boxed), 2, 1);
lean_closure_set(x_26, 0, x_3);
x_27 = l_Std_Sat_CNF_relabel___redArg(x_26, x_25);
return x_27;
}
}
}
}
lean_object* initialize_Std_Sat_CNF(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
