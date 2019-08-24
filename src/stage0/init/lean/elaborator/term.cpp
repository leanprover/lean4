// Lean compiler output
// Module: init.lean.elaborator.term
// Imports: init.lean.elaborator.alias init.lean.elaborator.basic init.lean.elaborator.preterm
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
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_elabList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_runIOUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabList___closed__3;
lean_object* l_Lean_Elab_elabList(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabTermAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l_Array_uget(lean_object*, lean_object*, size_t, lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_termElabAttribute;
lean_object* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2___boxed(lean_object*, lean_object*);
size_t lean_name_hash_usize(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabTermAux___main___closed__1;
lean_object* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_Elab_elabList___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_list___elambda__1___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabTermAux___main___closed__2;
lean_object* l_Lean_Elab_elabTermAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabList(lean_object*);
lean_object* l_IO_print___at_Lean_Elab_elabList___spec__2(lean_object*, lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_fset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabTermAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_oldElaborate(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabList___closed__2;
extern lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabList___closed__1;
lean_object* l_Lean_Elab_elabTermAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_box_usize(x_6);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(x_8, x_2);
return x_9;
}
}
}
lean_object* l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Array_empty___closed__1;
x_10 = x_2;
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_Array_empty___closed__1;
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = x_16;
x_18 = lean_array_fset(x_2, x_1, x_17);
x_19 = lean_box(0);
x_20 = 1;
lean_inc(x_3);
lean_inc(x_15);
x_21 = l_Lean_Elab_elabTermAux___main(x_15, x_19, x_20, x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_21, 0, x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = x_23;
x_27 = lean_array_fset(x_18, x_1, x_26);
lean_dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_1, x_32);
x_34 = x_29;
x_35 = lean_array_fset(x_18, x_1, x_34);
lean_dec(x_1);
x_1 = x_33;
x_2 = x_35;
x_4 = x_31;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_elabTermAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term elaborator failed, unexpected syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabTermAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabTermAux___main___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabTermAux___main(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_inc(x_9);
lean_ctor_set(x_5, 0, x_11);
x_12 = l_Lean_termElabAttribute;
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_PersistentEnvExtension_getState___rarg(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(x_15, x_6);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_21 = l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(x_20, x_7, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_1, 1, x_23);
if (x_3 == 0)
{
lean_object* x_25; 
lean_dec(x_24);
x_25 = l_Lean_Elab_oldElaborate(x_1, x_2, x_4, x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_1, 1, x_38);
if (x_3 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
x_41 = l_Lean_Elab_oldElaborate(x_1, x_2, x_4, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_39);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_56 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_57 = l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(x_56, x_7, x_4, x_5);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
lean_inc(x_59);
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_58);
if (x_3 == 0)
{
lean_object* x_63; 
lean_dec(x_59);
x_63 = l_Lean_Elab_oldElaborate(x_62, x_2, x_4, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_67, 0, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_61);
lean_dec(x_4);
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_59);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_76 = x_57;
} else {
 lean_dec_ref(x_57);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_7);
lean_dec(x_6);
x_78 = lean_ctor_get(x_16, 0);
lean_inc(x_78);
lean_dec(x_16);
x_79 = lean_apply_4(x_78, x_1, x_2, x_4, x_5);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_5, 1);
lean_inc(x_80);
lean_dec(x_5);
x_81 = lean_box(0);
lean_inc(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_termElabAttribute;
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
lean_dec(x_80);
x_86 = l_Lean_PersistentEnvExtension_getState___rarg(x_84, x_85);
lean_dec(x_85);
x_87 = l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(x_86, x_6);
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_88 = x_1;
} else {
 lean_dec_ref(x_1);
 x_88 = lean_box(0);
}
x_89 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_90 = l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(x_89, x_7, x_4, x_82);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
lean_inc(x_92);
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_81);
lean_ctor_set(x_94, 1, x_92);
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_6);
lean_ctor_set(x_95, 1, x_91);
if (x_3 == 0)
{
lean_object* x_96; 
lean_dec(x_92);
x_96 = l_Lean_Elab_oldElaborate(x_95, x_2, x_4, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_100, 0, x_97);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_104 = x_96;
} else {
 lean_dec_ref(x_96);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_94);
lean_dec(x_4);
lean_dec(x_2);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_92);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_107 = lean_ctor_get(x_90, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_109 = x_90;
} else {
 lean_dec_ref(x_90);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_7);
lean_dec(x_6);
x_111 = lean_ctor_get(x_87, 0);
lean_inc(x_111);
lean_dec(x_87);
x_112 = lean_apply_4(x_111, x_1, x_2, x_4, x_82);
return x_112;
}
}
}
case 4:
{
uint8_t x_113; 
lean_dec(x_4);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_5);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_5, 0);
lean_dec(x_114);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_5, 1);
lean_inc(x_115);
lean_dec(x_5);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
default: 
{
lean_dec(x_4);
lean_dec(x_2);
if (x_3 == 0)
{
uint8_t x_117; 
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_5);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_5, 0);
lean_dec(x_118);
x_119 = l_Lean_Elab_elabTermAux___main___closed__2;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_119);
return x_5;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_5, 1);
lean_inc(x_120);
lean_dec(x_5);
x_121 = l_Lean_Elab_elabTermAux___main___closed__2;
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_5);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_5, 0);
lean_dec(x_124);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_5, 1);
lean_inc(x_125);
lean_dec(x_5);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabTermAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_elabTermAux___main(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_elabTermAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_elabTermAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_elabTermAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_elabTermAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_elabTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_elabTermAux___main(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_IO_print___at_Lean_Elab_elabList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
x_6 = lean_io_prim_put_str(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_println___at_Lean_Elab_elabList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at_Lean_Elab_elabList___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_io_prim_put_str(x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_io_prim_put_str(x_12, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Elab_elabList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_println___at_Lean_Elab_elabList___spec__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_runIOUnsafe___rarg(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_elabList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabList(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabList");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabList___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabList___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_list___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabList___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabList___closed__3;
x_5 = l_Lean_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_init_lean_elaborator_alias(lean_object*);
lean_object* initialize_init_lean_elaborator_basic(lean_object*);
lean_object* initialize_init_lean_elaborator_preterm(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_elaborator_term(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_alias(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_preterm(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Elab_elabTermAux___main___closed__1 = _init_l_Lean_Elab_elabTermAux___main___closed__1();
lean_mark_persistent(l_Lean_Elab_elabTermAux___main___closed__1);
l_Lean_Elab_elabTermAux___main___closed__2 = _init_l_Lean_Elab_elabTermAux___main___closed__2();
lean_mark_persistent(l_Lean_Elab_elabTermAux___main___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabList___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabList___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabList___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabList___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabList___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabList___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabList(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
