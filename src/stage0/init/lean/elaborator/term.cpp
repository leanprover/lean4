// Lean compiler output
// Module: init.lean.elaborator.term
// Imports: init.lean.elaborator.alias init.lean.elaborator.basic init.lean.elaborator.preterm
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_Elab_elabList___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabList___closed__3;
obj* l_Lean_Elab_elabList(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_elabTermAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___rarg(obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
extern obj* l_Lean_Options_empty;
extern obj* l_Lean_termElabAttribute;
obj* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3___boxed(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2___boxed(obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_Elab_elabTermAux___main___closed__1;
obj* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(obj*, obj*);
obj* l_IO_println___at_Lean_Elab_elabList___spec__1(obj*, obj*);
extern "C" uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Lean_addBuiltinTermElab(obj*, obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
extern obj* l_Lean_Parser_Term_list___elambda__1___closed__2;
extern "C" obj* lean_nat_add(obj*, obj*);
obj* l_Lean_Elab_elabTermAux___main___closed__2;
obj* l_Lean_Elab_elabTermAux___main(obj*, obj*, uint8, obj*, obj*);
extern "C" usize lean_usize_modn(usize, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabList(obj*);
obj* l_IO_print___at_Lean_Elab_elabList___spec__2(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_elabTerm(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(obj*, obj*);
obj* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Elab_elabTermAux(obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_Elab_oldElaborate(obj*, obj*, obj*, obj*);
extern obj* l_IO_println___rarg___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabList___closed__2;
extern obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabList___closed__1;
obj* l_Lean_Elab_elabTermAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
obj* x_9; 
lean::inc(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_5);
return x_9;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(x_5, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
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
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(x_8, x_2);
return x_9;
}
}
}
obj* l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = l_Array_empty___closed__1;
x_10 = x_2;
lean::cnstr_set(x_4, 0, x_10);
return x_4;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_12 = l_Array_empty___closed__1;
x_13 = x_2;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean::box(0);
lean::inc(x_15);
x_17 = x_16;
x_18 = lean_array_fset(x_2, x_1, x_17);
x_19 = lean::box(0);
x_20 = 1;
lean::inc(x_3);
lean::inc(x_15);
x_21 = l_Lean_Elab_elabTermAux___main(x_15, x_19, x_20, x_3, x_4);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_16);
x_24 = lean::mk_nat_obj(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = x_23;
x_27 = lean_array_fset(x_18, x_1, x_26);
lean::dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_4 = x_21;
goto _start;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_21, 0);
x_30 = lean::cnstr_get(x_21, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_21);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_16);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean_nat_add(x_1, x_32);
x_34 = x_29;
x_35 = lean_array_fset(x_18, x_1, x_34);
lean::dec(x_1);
x_1 = x_33;
x_2 = x_35;
x_4 = x_31;
goto _start;
}
}
else
{
uint8 x_37; 
lean::dec(x_18);
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_1);
x_37 = !lean::is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_21, 0);
x_39 = lean::cnstr_get(x_21, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_21);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
obj* _init_l_Lean_Elab_elabTermAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term elaborator failed, unexpected syntax");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabTermAux___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabTermAux___main___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Elab_elabTermAux___main(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_5, 1);
x_10 = lean::cnstr_get(x_5, 0);
lean::dec(x_10);
x_11 = lean::box(0);
lean::inc(x_9);
lean::cnstr_set(x_5, 0, x_11);
x_12 = l_Lean_termElabAttribute;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_15 = l_Lean_PersistentEnvExtension_getState___rarg(x_13, x_14);
lean::dec(x_14);
x_16 = l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(x_15, x_6);
lean::dec(x_15);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_1);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_1, 1);
lean::dec(x_18);
x_19 = lean::cnstr_get(x_1, 0);
lean::dec(x_19);
x_20 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_21 = l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(x_20, x_7, x_4, x_5);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_1, 1, x_23);
if (x_3 == 0)
{
obj* x_25; 
lean::dec(x_24);
x_25 = l_Lean_Elab_oldElaborate(x_1, x_2, x_4, x_21);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
x_28 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_25, 0, x_28);
return x_25;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_25, 0);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_25);
x_31 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_31, 0, x_29);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_25, 0);
x_35 = lean::cnstr_get(x_25, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_25);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
obj* x_37; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_2);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_24);
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_21, 0);
x_39 = lean::cnstr_get(x_21, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_21);
lean::inc(x_39);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_11);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set(x_1, 1, x_38);
if (x_3 == 0)
{
obj* x_41; 
lean::dec(x_39);
x_41 = l_Lean_Elab_oldElaborate(x_1, x_2, x_4, x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_44 = x_41;
} else {
 lean::dec_ref(x_41);
 x_44 = lean::box(0);
}
x_45 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_41, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_49 = x_41;
} else {
 lean::dec_ref(x_41);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
}
else
{
obj* x_51; 
lean::dec(x_40);
lean::dec(x_4);
lean::dec(x_2);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_1);
lean::cnstr_set(x_51, 1, x_39);
return x_51;
}
}
}
else
{
uint8 x_52; 
lean::free_heap_obj(x_1);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_52 = !lean::is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_21, 0);
x_54 = lean::cnstr_get(x_21, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_21);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_1);
x_56 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_57 = l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(x_56, x_7, x_4, x_5);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_60 = x_57;
} else {
 lean::dec_ref(x_57);
 x_60 = lean::box(0);
}
lean::inc(x_59);
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_11);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_6);
lean::cnstr_set(x_62, 1, x_58);
if (x_3 == 0)
{
obj* x_63; 
lean::dec(x_59);
x_63 = l_Lean_Elab_oldElaborate(x_62, x_2, x_4, x_61);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_66 = x_63;
} else {
 lean::dec_ref(x_63);
 x_66 = lean::box(0);
}
x_67 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_65);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_69 = lean::cnstr_get(x_63, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_63, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_71 = x_63;
} else {
 lean::dec_ref(x_63);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
}
else
{
obj* x_73; 
lean::dec(x_61);
lean::dec(x_4);
lean::dec(x_2);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_62);
lean::cnstr_set(x_73, 1, x_59);
return x_73;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_74 = lean::cnstr_get(x_57, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_57, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_76 = x_57;
} else {
 lean::dec_ref(x_57);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
obj* x_78; obj* x_79; 
lean::dec(x_7);
lean::dec(x_6);
x_78 = lean::cnstr_get(x_16, 0);
lean::inc(x_78);
lean::dec(x_16);
x_79 = lean::apply_4(x_78, x_1, x_2, x_4, x_5);
return x_79;
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_80 = lean::cnstr_get(x_5, 1);
lean::inc(x_80);
lean::dec(x_5);
x_81 = lean::box(0);
lean::inc(x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = l_Lean_termElabAttribute;
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_80, 0);
lean::inc(x_85);
lean::dec(x_80);
x_86 = l_Lean_PersistentEnvExtension_getState___rarg(x_84, x_85);
lean::dec(x_85);
x_87 = l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(x_86, x_6);
lean::dec(x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_89; obj* x_90; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_88 = x_1;
} else {
 lean::dec_ref(x_1);
 x_88 = lean::box(0);
}
x_89 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_90 = l_Array_ummapAux___main___at_Lean_Elab_elabTermAux___main___spec__4(x_89, x_7, x_4, x_82);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_90, 1);
lean::inc(x_92);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 x_93 = x_90;
} else {
 lean::dec_ref(x_90);
 x_93 = lean::box(0);
}
lean::inc(x_92);
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_81);
lean::cnstr_set(x_94, 1, x_92);
if (lean::is_scalar(x_88)) {
 x_95 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_95 = x_88;
}
lean::cnstr_set(x_95, 0, x_6);
lean::cnstr_set(x_95, 1, x_91);
if (x_3 == 0)
{
obj* x_96; 
lean::dec(x_92);
x_96 = l_Lean_Elab_oldElaborate(x_95, x_2, x_4, x_94);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_96, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_99 = x_96;
} else {
 lean::dec_ref(x_96);
 x_99 = lean::box(0);
}
x_100 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_100, 0, x_97);
if (lean::is_scalar(x_99)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_99;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_102 = lean::cnstr_get(x_96, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_96, 1);
lean::inc(x_103);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_104 = x_96;
} else {
 lean::dec_ref(x_96);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
lean::cnstr_set(x_105, 1, x_103);
return x_105;
}
}
else
{
obj* x_106; 
lean::dec(x_94);
lean::dec(x_4);
lean::dec(x_2);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_95);
lean::cnstr_set(x_106, 1, x_92);
return x_106;
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_88);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_107 = lean::cnstr_get(x_90, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_90, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 x_109 = x_90;
} else {
 lean::dec_ref(x_90);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_108);
return x_110;
}
}
else
{
obj* x_111; obj* x_112; 
lean::dec(x_7);
lean::dec(x_6);
x_111 = lean::cnstr_get(x_87, 0);
lean::inc(x_111);
lean::dec(x_87);
x_112 = lean::apply_4(x_111, x_1, x_2, x_4, x_82);
return x_112;
}
}
}
case 4:
{
uint8 x_113; 
lean::dec(x_4);
lean::dec(x_2);
x_113 = !lean::is_exclusive(x_5);
if (x_113 == 0)
{
obj* x_114; 
x_114 = lean::cnstr_get(x_5, 0);
lean::dec(x_114);
lean::cnstr_set(x_5, 0, x_1);
return x_5;
}
else
{
obj* x_115; obj* x_116; 
x_115 = lean::cnstr_get(x_5, 1);
lean::inc(x_115);
lean::dec(x_5);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_1);
lean::cnstr_set(x_116, 1, x_115);
return x_116;
}
}
default: 
{
lean::dec(x_4);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_117; 
lean::dec(x_1);
x_117 = !lean::is_exclusive(x_5);
if (x_117 == 0)
{
obj* x_118; obj* x_119; 
x_118 = lean::cnstr_get(x_5, 0);
lean::dec(x_118);
x_119 = l_Lean_Elab_elabTermAux___main___closed__2;
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_119);
return x_5;
}
else
{
obj* x_120; obj* x_121; obj* x_122; 
x_120 = lean::cnstr_get(x_5, 1);
lean::inc(x_120);
lean::dec(x_5);
x_121 = l_Lean_Elab_elabTermAux___main___closed__2;
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8 x_123; 
x_123 = !lean::is_exclusive(x_5);
if (x_123 == 0)
{
obj* x_124; 
x_124 = lean::cnstr_get(x_5, 0);
lean::dec(x_124);
lean::cnstr_set(x_5, 0, x_1);
return x_5;
}
else
{
obj* x_125; obj* x_126; 
x_125 = lean::cnstr_get(x_5, 1);
lean::inc(x_125);
lean::dec(x_5);
x_126 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_126, 0, x_1);
lean::cnstr_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
obj* l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_elabTermAux___main___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_elabTermAux___main___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find___at_Lean_Elab_elabTermAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Elab_elabTermAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
lean::dec(x_3);
x_7 = l_Lean_Elab_elabTermAux___main(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Elab_elabTermAux(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Elab_elabTermAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Elab_elabTermAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
lean::dec(x_3);
x_7 = l_Lean_Elab_elabTermAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Elab_elabTerm(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_elabTermAux___main(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
obj* l_IO_print___at_Lean_Elab_elabList___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
x_6 = lean_io_prim_put_str(x_5, x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_IO_println___at_Lean_Elab_elabList___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_print___at_Lean_Elab_elabList___spec__2(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_io_prim_put_str(x_7, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_io_prim_put_str(x_12, x_11);
return x_13;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_Lean_Elab_elabList(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_Lean_Elab_elabList___spec__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_runIOUnsafe___rarg(x_5, x_3, x_4);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::dec(x_8);
lean::cnstr_set(x_6, 0, x_1);
return x_6;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8 x_11; 
lean::dec(x_1);
x_11 = !lean::is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_6);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_Lean_Elab_elabList___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Elab_elabList(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabList");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabList___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabList___boxed), 4, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabList(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_list___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabList___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabList___closed__3;
x_5 = l_Lean_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* initialize_init_lean_elaborator_alias(obj*);
obj* initialize_init_lean_elaborator_basic(obj*);
obj* initialize_init_lean_elaborator_preterm(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_term(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_alias(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_preterm(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Elab_elabTermAux___main___closed__1 = _init_l_Lean_Elab_elabTermAux___main___closed__1();
lean::mark_persistent(l_Lean_Elab_elabTermAux___main___closed__1);
l_Lean_Elab_elabTermAux___main___closed__2 = _init_l_Lean_Elab_elabTermAux___main___closed__2();
lean::mark_persistent(l_Lean_Elab_elabTermAux___main___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabList___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabList___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabList___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabList___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabList___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabList___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabList___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabList(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
