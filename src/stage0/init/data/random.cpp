// Lean compiler output
// Module: init.data.random
// Imports: init.io init.data.int.default
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
obj* l_mkStdGen(obj*);
obj* l_stdNext___main___closed__5;
obj* l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Sigma_HasRepr___rarg___closed__1;
namespace lean {
obj* nat2int(obj*);
}
obj* l_IO_mkStdGenRef___closed__1;
obj* l_StdGen_HasRepr(obj*);
namespace lean {
obj* int_sub(obj*, obj*);
}
obj* l_randNat(obj*);
obj* l_stdNext___main___closed__7;
obj* l___private_init_data_random_1__randNatAux(obj*);
obj* l_stdNext___main___closed__8;
obj* l_IO_rand___boxed(obj*, obj*, obj*);
obj* l_stdSplit(obj*);
obj* l_StdGen_RandomGen___lambda__1___boxed(obj*);
obj* l_Int_toNat___main(obj*);
obj* l___private_init_data_random_1__randNatAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_randNat___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_StdGen_RandomGen___lambda__1(obj*);
obj* l_StdGen_RandomGen;
obj* l_stdNext___main___closed__6;
obj* l_randBool___rarg(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_randBool(obj*);
obj* l_IO_setRandSeed___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern obj* l_List_reprAux___main___rarg___closed__1;
namespace lean {
obj* int_add(obj*, obj*);
}
obj* l_randNat___at_IO_rand___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_stdNext(obj*);
obj* l_stdNext___main___closed__9;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_stdNext___main___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_data_random_1__randNatAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_stdRange;
obj* l_stdNext___main___closed__4;
obj* l_stdNext___main(obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_IO_stdGenRef;
extern obj* l_Sigma_HasRepr___rarg___closed__2;
obj* l_mkStdGen___boxed(obj*);
obj* l___private_init_data_random_1__randNatAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_rand(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_stdSplit___main(obj*);
namespace lean {
obj* int_mul(obj*, obj*);
}
obj* l___private_init_data_random_1__randNatAux___main(obj*);
extern obj* l_Int_zero;
obj* l_IO_mkStdGenRef(obj*);
obj* l_randNat___rarg(obj*, obj*, obj*, obj*);
obj* l_stdNext___main___closed__3;
obj* l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l___private_init_data_random_1__randNatAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_stdNext___main___closed__2;
extern obj* l_Int_one;
obj* l_randNat___at_IO_rand___spec__1(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_IO_setRandSeed(obj*, obj*);
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
namespace lean {
obj* int_div(obj*, obj*);
}
namespace lean {
obj* int_mod(obj*, obj*);
}
obj* _init_l_stdRange() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::mk_nat_obj(2147483562u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_StdGen_HasRepr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Nat_repr(x_2);
x_5 = l_Sigma_HasRepr___rarg___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean::string_append(x_6, x_7);
x_9 = l_Nat_repr(x_3);
x_10 = lean::string_append(x_8, x_9);
lean::dec(x_9);
x_11 = l_Sigma_HasRepr___rarg___closed__2;
x_12 = lean::string_append(x_10, x_11);
return x_12;
}
}
obj* _init_l_stdNext___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_1);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_4);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_1);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_8);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_1);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_1);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_13);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_1);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_17);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_1);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_21);
lean::dec(x_21);
return x_22;
}
}
obj* _init_l_stdNext___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_1);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_1);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_1);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_1);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_15);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_1);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_1);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_1);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_22);
lean::dec(x_22);
return x_23;
}
}
obj* _init_l_stdNext___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_1);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_4);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_1);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_1);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_8);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_1);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_1);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_13);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_1);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_15);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_1);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_17);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_19);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_1);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_21);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_1);
lean::dec(x_22);
return x_23;
}
}
obj* _init_l_stdNext___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_1);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_4);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_1);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_1);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_1);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_13);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_1);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_17);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_1);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_1);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_22);
lean::dec(x_22);
return x_23;
}
}
obj* _init_l_stdNext___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_1);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_1);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_1);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_1);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_1);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_1);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_1);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_1);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_21);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_1);
lean::dec(x_22);
x_24 = lean::int_add(x_23, x_23);
lean::dec(x_23);
x_25 = lean::int_add(x_24, x_24);
lean::dec(x_24);
return x_25;
}
}
obj* _init_l_stdNext___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_1);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_1);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_1);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_8);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_1);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_1);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_1);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_1);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_1);
lean::dec(x_19);
return x_20;
}
}
obj* _init_l_stdNext___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_1);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_1);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_1);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_1);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_1);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_1);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_13);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_1);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_15);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_1);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_17);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_1);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_19);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_1);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_21);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_1);
lean::dec(x_22);
x_24 = lean::int_add(x_23, x_23);
lean::dec(x_23);
x_25 = lean::int_add(x_24, x_1);
lean::dec(x_24);
x_26 = lean::int_add(x_25, x_25);
lean::dec(x_25);
x_27 = lean::int_add(x_26, x_1);
lean::dec(x_26);
x_28 = lean::int_add(x_27, x_27);
lean::dec(x_27);
x_29 = lean::int_add(x_28, x_1);
lean::dec(x_28);
x_30 = lean::int_add(x_29, x_29);
lean::dec(x_29);
x_31 = lean::int_add(x_30, x_1);
lean::dec(x_30);
x_32 = lean::int_add(x_31, x_31);
lean::dec(x_31);
x_33 = lean::int_add(x_32, x_1);
lean::dec(x_32);
x_34 = lean::int_add(x_33, x_33);
lean::dec(x_33);
x_35 = lean::int_add(x_34, x_1);
lean::dec(x_34);
x_36 = lean::int_add(x_35, x_35);
lean::dec(x_35);
x_37 = lean::int_add(x_36, x_1);
lean::dec(x_36);
x_38 = lean::int_add(x_37, x_37);
lean::dec(x_37);
x_39 = lean::int_add(x_38, x_1);
lean::dec(x_38);
x_40 = lean::int_add(x_39, x_39);
lean::dec(x_39);
x_41 = lean::int_add(x_40, x_1);
lean::dec(x_40);
x_42 = lean::int_add(x_41, x_41);
lean::dec(x_41);
x_43 = lean::int_add(x_42, x_1);
lean::dec(x_42);
x_44 = lean::int_add(x_43, x_43);
lean::dec(x_43);
x_45 = lean::int_add(x_44, x_1);
lean::dec(x_44);
x_46 = lean::int_add(x_45, x_45);
lean::dec(x_45);
x_47 = lean::int_add(x_46, x_1);
lean::dec(x_46);
x_48 = lean::int_add(x_47, x_47);
lean::dec(x_47);
x_49 = lean::int_add(x_48, x_48);
lean::dec(x_48);
x_50 = lean::int_add(x_49, x_1);
lean::dec(x_49);
x_51 = lean::int_add(x_50, x_50);
lean::dec(x_50);
x_52 = lean::int_add(x_51, x_51);
lean::dec(x_51);
x_53 = lean::int_add(x_52, x_1);
lean::dec(x_52);
x_54 = lean::int_add(x_53, x_53);
lean::dec(x_53);
x_55 = lean::int_add(x_54, x_54);
lean::dec(x_54);
x_56 = lean::int_add(x_55, x_1);
lean::dec(x_55);
x_57 = lean::int_add(x_56, x_56);
lean::dec(x_56);
return x_57;
}
}
obj* _init_l_stdNext___main___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_1);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_1);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_1);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_1);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_1);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_1);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_13);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_1);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_15);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_1);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_17);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_1);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_19);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_1);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_21);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_1);
lean::dec(x_22);
x_24 = lean::int_add(x_23, x_23);
lean::dec(x_23);
x_25 = lean::int_add(x_24, x_1);
lean::dec(x_24);
x_26 = lean::int_add(x_25, x_25);
lean::dec(x_25);
x_27 = lean::int_add(x_26, x_1);
lean::dec(x_26);
x_28 = lean::int_add(x_27, x_27);
lean::dec(x_27);
x_29 = lean::int_add(x_28, x_1);
lean::dec(x_28);
x_30 = lean::int_add(x_29, x_29);
lean::dec(x_29);
x_31 = lean::int_add(x_30, x_1);
lean::dec(x_30);
x_32 = lean::int_add(x_31, x_31);
lean::dec(x_31);
x_33 = lean::int_add(x_32, x_1);
lean::dec(x_32);
x_34 = lean::int_add(x_33, x_33);
lean::dec(x_33);
x_35 = lean::int_add(x_34, x_1);
lean::dec(x_34);
x_36 = lean::int_add(x_35, x_35);
lean::dec(x_35);
x_37 = lean::int_add(x_36, x_1);
lean::dec(x_36);
x_38 = lean::int_add(x_37, x_37);
lean::dec(x_37);
x_39 = lean::int_add(x_38, x_1);
lean::dec(x_38);
x_40 = lean::int_add(x_39, x_39);
lean::dec(x_39);
x_41 = lean::int_add(x_40, x_1);
lean::dec(x_40);
x_42 = lean::int_add(x_41, x_41);
lean::dec(x_41);
x_43 = lean::int_add(x_42, x_1);
lean::dec(x_42);
x_44 = lean::int_add(x_43, x_43);
lean::dec(x_43);
x_45 = lean::int_add(x_44, x_1);
lean::dec(x_44);
x_46 = lean::int_add(x_45, x_45);
lean::dec(x_45);
x_47 = lean::int_add(x_46, x_46);
lean::dec(x_46);
x_48 = lean::int_add(x_47, x_47);
lean::dec(x_47);
x_49 = lean::int_add(x_48, x_48);
lean::dec(x_48);
x_50 = lean::int_add(x_49, x_49);
lean::dec(x_49);
x_51 = lean::int_add(x_50, x_50);
lean::dec(x_50);
x_52 = lean::int_add(x_51, x_1);
lean::dec(x_51);
x_53 = lean::int_add(x_52, x_52);
lean::dec(x_52);
x_54 = lean::int_add(x_53, x_1);
lean::dec(x_53);
x_55 = lean::int_add(x_54, x_54);
lean::dec(x_54);
x_56 = lean::int_add(x_55, x_1);
lean::dec(x_55);
return x_56;
}
}
obj* _init_l_stdNext___main___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_1 = l_Int_one;
x_2 = lean::int_add(x_1, x_1);
x_3 = lean::int_add(x_2, x_1);
lean::dec(x_2);
x_4 = lean::int_add(x_3, x_3);
lean::dec(x_3);
x_5 = lean::int_add(x_4, x_1);
lean::dec(x_4);
x_6 = lean::int_add(x_5, x_5);
lean::dec(x_5);
x_7 = lean::int_add(x_6, x_1);
lean::dec(x_6);
x_8 = lean::int_add(x_7, x_7);
lean::dec(x_7);
x_9 = lean::int_add(x_8, x_1);
lean::dec(x_8);
x_10 = lean::int_add(x_9, x_9);
lean::dec(x_9);
x_11 = lean::int_add(x_10, x_1);
lean::dec(x_10);
x_12 = lean::int_add(x_11, x_11);
lean::dec(x_11);
x_13 = lean::int_add(x_12, x_1);
lean::dec(x_12);
x_14 = lean::int_add(x_13, x_13);
lean::dec(x_13);
x_15 = lean::int_add(x_14, x_1);
lean::dec(x_14);
x_16 = lean::int_add(x_15, x_15);
lean::dec(x_15);
x_17 = lean::int_add(x_16, x_1);
lean::dec(x_16);
x_18 = lean::int_add(x_17, x_17);
lean::dec(x_17);
x_19 = lean::int_add(x_18, x_1);
lean::dec(x_18);
x_20 = lean::int_add(x_19, x_19);
lean::dec(x_19);
x_21 = lean::int_add(x_20, x_1);
lean::dec(x_20);
x_22 = lean::int_add(x_21, x_21);
lean::dec(x_21);
x_23 = lean::int_add(x_22, x_1);
lean::dec(x_22);
x_24 = lean::int_add(x_23, x_23);
lean::dec(x_23);
x_25 = lean::int_add(x_24, x_1);
lean::dec(x_24);
x_26 = lean::int_add(x_25, x_25);
lean::dec(x_25);
x_27 = lean::int_add(x_26, x_1);
lean::dec(x_26);
x_28 = lean::int_add(x_27, x_27);
lean::dec(x_27);
x_29 = lean::int_add(x_28, x_1);
lean::dec(x_28);
x_30 = lean::int_add(x_29, x_29);
lean::dec(x_29);
x_31 = lean::int_add(x_30, x_1);
lean::dec(x_30);
x_32 = lean::int_add(x_31, x_31);
lean::dec(x_31);
x_33 = lean::int_add(x_32, x_1);
lean::dec(x_32);
x_34 = lean::int_add(x_33, x_33);
lean::dec(x_33);
x_35 = lean::int_add(x_34, x_1);
lean::dec(x_34);
x_36 = lean::int_add(x_35, x_35);
lean::dec(x_35);
x_37 = lean::int_add(x_36, x_1);
lean::dec(x_36);
x_38 = lean::int_add(x_37, x_37);
lean::dec(x_37);
x_39 = lean::int_add(x_38, x_1);
lean::dec(x_38);
x_40 = lean::int_add(x_39, x_39);
lean::dec(x_39);
x_41 = lean::int_add(x_40, x_1);
lean::dec(x_40);
x_42 = lean::int_add(x_41, x_41);
lean::dec(x_41);
x_43 = lean::int_add(x_42, x_1);
lean::dec(x_42);
x_44 = lean::int_add(x_43, x_43);
lean::dec(x_43);
x_45 = lean::int_add(x_44, x_1);
lean::dec(x_44);
x_46 = lean::int_add(x_45, x_45);
lean::dec(x_45);
x_47 = lean::int_add(x_46, x_1);
lean::dec(x_46);
x_48 = lean::int_add(x_47, x_47);
lean::dec(x_47);
x_49 = lean::int_add(x_48, x_48);
lean::dec(x_48);
x_50 = lean::int_add(x_49, x_1);
lean::dec(x_49);
x_51 = lean::int_add(x_50, x_50);
lean::dec(x_50);
x_52 = lean::int_add(x_51, x_51);
lean::dec(x_51);
x_53 = lean::int_add(x_52, x_1);
lean::dec(x_52);
x_54 = lean::int_add(x_53, x_53);
lean::dec(x_53);
x_55 = lean::int_add(x_54, x_54);
lean::dec(x_54);
x_56 = lean::int_add(x_55, x_1);
lean::dec(x_55);
x_57 = lean::int_add(x_56, x_56);
lean::dec(x_56);
x_58 = lean::int_add(x_57, x_1);
lean::dec(x_57);
return x_58;
}
}
obj* l_stdNext___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_4 = x_1;
} else {
 lean::dec_ref(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::nat2int(x_2);
x_6 = l_stdNext___main___closed__1;
x_7 = lean::int_div(x_5, x_6);
x_8 = lean::int_mul(x_7, x_6);
x_9 = lean::int_sub(x_5, x_8);
lean::dec(x_8);
lean::dec(x_5);
x_10 = l_stdNext___main___closed__2;
x_11 = lean::int_mul(x_10, x_9);
lean::dec(x_9);
x_12 = l_stdNext___main___closed__3;
x_13 = lean::int_mul(x_7, x_12);
lean::dec(x_7);
x_14 = lean::int_sub(x_11, x_13);
lean::dec(x_13);
lean::dec(x_11);
x_15 = l_Int_zero;
x_16 = lean::int_dec_lt(x_14, x_15);
x_17 = lean::nat2int(x_3);
x_18 = l_stdNext___main___closed__4;
x_19 = lean::int_div(x_17, x_18);
x_20 = lean::int_mul(x_19, x_18);
x_21 = lean::int_sub(x_17, x_20);
lean::dec(x_20);
lean::dec(x_17);
x_22 = l_stdNext___main___closed__5;
x_23 = lean::int_mul(x_22, x_21);
lean::dec(x_21);
x_24 = l_stdNext___main___closed__6;
x_25 = lean::int_mul(x_19, x_24);
lean::dec(x_19);
x_26 = lean::int_sub(x_23, x_25);
lean::dec(x_25);
lean::dec(x_23);
x_27 = lean::int_dec_lt(x_26, x_15);
if (x_16 == 0)
{
x_28 = x_14;
goto block_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_stdNext___main___closed__9;
x_49 = lean::int_add(x_14, x_48);
lean::dec(x_14);
x_28 = x_49;
goto block_47;
}
block_47:
{
obj* x_29; obj* x_30; 
x_29 = l_Int_toNat___main(x_28);
if (x_27 == 0)
{
x_30 = x_26;
goto block_44;
}
else
{
obj* x_45; obj* x_46; 
x_45 = l_stdNext___main___closed__8;
x_46 = lean::int_add(x_26, x_45);
lean::dec(x_26);
x_30 = x_46;
goto block_44;
}
block_44:
{
obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; 
x_31 = lean::int_sub(x_28, x_30);
lean::dec(x_28);
x_32 = l_Int_one;
x_33 = lean::int_dec_lt(x_31, x_32);
x_34 = l_Int_toNat___main(x_30);
lean::dec(x_30);
if (lean::is_scalar(x_4)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_4;
}
lean::cnstr_set(x_35, 0, x_29);
lean::cnstr_set(x_35, 1, x_34);
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = l_stdNext___main___closed__7;
x_37 = lean::int_mod(x_31, x_36);
lean::dec(x_31);
x_38 = l_Int_toNat___main(x_37);
lean::dec(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_35);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_40 = l_stdNext___main___closed__7;
x_41 = lean::int_add(x_31, x_40);
lean::dec(x_31);
x_42 = l_Int_toNat___main(x_41);
lean::dec(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_35);
return x_43;
}
}
}
}
}
obj* l_stdNext(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_stdNext___main(x_1);
return x_2;
}
}
obj* l_stdSplit___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; uint8 x_7; obj* x_8; uint8 x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::mk_nat_obj(2147483562u);
x_5 = lean::nat_dec_eq(x_2, x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_dec_eq(x_3, x_6);
lean::inc(x_1);
x_8 = l_stdNext___main(x_1);
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
lean::dec(x_8);
if (x_5 == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = lean::nat_add(x_2, x_6);
lean::dec(x_2);
lean::cnstr_set(x_12, 0, x_15);
if (x_7 == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::nat_sub(x_3, x_6);
lean::dec(x_3);
lean::cnstr_set(x_1, 1, x_16);
lean::cnstr_set(x_1, 0, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_1);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_3);
x_18 = lean::mk_nat_obj(2147483398u);
lean::cnstr_set(x_1, 1, x_18);
lean::cnstr_set(x_1, 0, x_14);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_1);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_12, 0);
x_21 = lean::cnstr_get(x_12, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_12);
x_22 = lean::nat_add(x_2, x_6);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
if (x_7 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::nat_sub(x_3, x_6);
lean::dec(x_3);
lean::cnstr_set(x_1, 1, x_24);
lean::cnstr_set(x_1, 0, x_20);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_1);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_3);
x_26 = lean::mk_nat_obj(2147483398u);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_20);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_1);
return x_27;
}
}
}
else
{
uint8 x_28; 
lean::dec(x_2);
x_28 = !lean::is_exclusive(x_12);
if (x_28 == 0)
{
obj* x_29; 
x_29 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_12, 0, x_6);
if (x_7 == 0)
{
obj* x_30; obj* x_31; 
x_30 = lean::nat_sub(x_3, x_6);
lean::dec(x_3);
lean::cnstr_set(x_1, 1, x_30);
lean::cnstr_set(x_1, 0, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_12);
lean::cnstr_set(x_31, 1, x_1);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_3);
x_32 = lean::mk_nat_obj(2147483398u);
lean::cnstr_set(x_1, 1, x_32);
lean::cnstr_set(x_1, 0, x_29);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_12);
lean::cnstr_set(x_33, 1, x_1);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_12, 0);
x_35 = lean::cnstr_get(x_12, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_12);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
if (x_7 == 0)
{
obj* x_37; obj* x_38; 
x_37 = lean::nat_sub(x_3, x_6);
lean::dec(x_3);
lean::cnstr_set(x_1, 1, x_37);
lean::cnstr_set(x_1, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_1);
return x_38;
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_3);
x_39 = lean::mk_nat_obj(2147483398u);
lean::cnstr_set(x_1, 1, x_39);
lean::cnstr_set(x_1, 0, x_34);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_1);
return x_40;
}
}
}
}
else
{
obj* x_41; 
lean::dec(x_1);
x_41 = lean::cnstr_get(x_8, 1);
lean::inc(x_41);
lean::dec(x_8);
if (x_5 == 0)
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
x_45 = lean::nat_add(x_2, x_6);
lean::dec(x_2);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_43);
if (x_7 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::nat_sub(x_3, x_6);
lean::dec(x_3);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_42);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_3);
x_50 = lean::mk_nat_obj(2147483398u);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_42);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_46);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_2);
x_53 = lean::cnstr_get(x_41, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_41, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_55 = x_41;
} else {
 lean::dec_ref(x_41);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_6);
lean::cnstr_set(x_56, 1, x_54);
if (x_7 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::nat_sub(x_3, x_6);
lean::dec(x_3);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_3);
x_60 = lean::mk_nat_obj(2147483398u);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_53);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_56);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
obj* l_stdSplit(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_stdSplit___main(x_1);
return x_2;
}
}
obj* l_StdGen_RandomGen___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_stdRange;
return x_2;
}
}
obj* _init_l_StdGen_RandomGen() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_StdGen_RandomGen___lambda__1___boxed), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_stdNext), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_stdSplit), 1, 0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_StdGen_RandomGen___lambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_StdGen_RandomGen___lambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_mkStdGen(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::mk_nat_obj(2147483562u);
x_3 = lean::nat_div(x_1, x_2);
x_4 = lean::nat_mod(x_1, x_2);
x_5 = lean::mk_nat_obj(2147483398u);
x_6 = lean::nat_mod(x_3, x_5);
lean::dec(x_3);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_4, x_7);
lean::dec(x_4);
x_9 = lean::nat_add(x_6, x_7);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_mkStdGen___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkStdGen(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_random_1__randNatAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
lean::dec(x_5);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::apply_1(x_12, x_11);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean::nat_mul(x_10, x_3);
lean::dec(x_10);
x_17 = lean::nat_add(x_9, x_8);
lean::dec(x_9);
x_18 = lean::nat_div(x_17, x_3);
lean::dec(x_17);
x_19 = lean::nat_sub(x_18, x_8);
lean::dec(x_18);
x_20 = lean::nat_sub(x_15, x_2);
lean::dec(x_15);
x_21 = lean::nat_add(x_16, x_20);
lean::dec(x_20);
lean::dec(x_16);
lean::cnstr_set(x_13, 0, x_21);
x_4 = x_19;
x_5 = x_13;
goto _start;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_23 = lean::cnstr_get(x_13, 0);
x_24 = lean::cnstr_get(x_13, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_13);
x_25 = lean::nat_mul(x_10, x_3);
lean::dec(x_10);
x_26 = lean::nat_add(x_9, x_8);
lean::dec(x_9);
x_27 = lean::nat_div(x_26, x_3);
lean::dec(x_26);
x_28 = lean::nat_sub(x_27, x_8);
lean::dec(x_27);
x_29 = lean::nat_sub(x_23, x_2);
lean::dec(x_23);
x_30 = lean::nat_add(x_25, x_29);
lean::dec(x_29);
lean::dec(x_25);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_24);
x_4 = x_28;
x_5 = x_31;
goto _start;
}
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
}
obj* l___private_init_data_random_1__randNatAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_random_1__randNatAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_random_1__randNatAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_random_1__randNatAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_data_random_1__randNatAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_random_1__randNatAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_data_random_1__randNatAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_random_1__randNatAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_random_1__randNatAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_random_1__randNatAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_randNat___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
x_5 = lean::nat_dec_lt(x_4, x_3);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::inc(x_2);
x_7 = lean::apply_1(x_6, x_2);
if (x_5 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = lean::cnstr_get(x_7, 1);
x_11 = lean::nat_sub(x_10, x_9);
lean::dec(x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_11, x_12);
lean::dec(x_11);
x_14 = lean::nat_sub(x_4, x_3);
x_15 = lean::nat_add(x_14, x_12);
lean::dec(x_14);
x_16 = lean::mk_nat_obj(1000u);
x_17 = lean::nat_mul(x_15, x_16);
x_18 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 0, x_18);
x_19 = l___private_init_data_random_1__randNatAux___main___rarg(x_1, x_9, x_13, x_17, x_7);
lean::dec(x_13);
lean::dec(x_9);
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = lean::nat_mod(x_21, x_15);
lean::dec(x_15);
lean::dec(x_21);
x_23 = lean::nat_add(x_3, x_22);
lean::dec(x_22);
lean::cnstr_set(x_19, 0, x_23);
return x_19;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_19, 0);
x_25 = lean::cnstr_get(x_19, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_19);
x_26 = lean::nat_mod(x_24, x_15);
lean::dec(x_15);
lean::dec(x_24);
x_27 = lean::nat_add(x_3, x_26);
lean::dec(x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_29 = lean::cnstr_get(x_7, 0);
x_30 = lean::cnstr_get(x_7, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_7);
x_31 = lean::nat_sub(x_30, x_29);
lean::dec(x_30);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::nat_add(x_31, x_32);
lean::dec(x_31);
x_34 = lean::nat_sub(x_4, x_3);
x_35 = lean::nat_add(x_34, x_32);
lean::dec(x_34);
x_36 = lean::mk_nat_obj(1000u);
x_37 = lean::nat_mul(x_35, x_36);
x_38 = lean::mk_nat_obj(0u);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_2);
x_40 = l___private_init_data_random_1__randNatAux___main___rarg(x_1, x_29, x_33, x_37, x_39);
lean::dec(x_33);
lean::dec(x_29);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_43 = x_40;
} else {
 lean::dec_ref(x_40);
 x_43 = lean::box(0);
}
x_44 = lean::nat_mod(x_41, x_35);
lean::dec(x_35);
lean::dec(x_41);
x_45 = lean::nat_add(x_3, x_44);
lean::dec(x_44);
if (lean::is_scalar(x_43)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_43;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
}
else
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_7);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; uint8 x_59; 
x_48 = lean::cnstr_get(x_7, 0);
x_49 = lean::cnstr_get(x_7, 1);
x_50 = lean::nat_sub(x_49, x_48);
lean::dec(x_49);
x_51 = lean::mk_nat_obj(1u);
x_52 = lean::nat_add(x_50, x_51);
lean::dec(x_50);
x_53 = lean::nat_sub(x_3, x_4);
x_54 = lean::nat_add(x_53, x_51);
lean::dec(x_53);
x_55 = lean::mk_nat_obj(1000u);
x_56 = lean::nat_mul(x_54, x_55);
x_57 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 0, x_57);
x_58 = l___private_init_data_random_1__randNatAux___main___rarg(x_1, x_48, x_52, x_56, x_7);
lean::dec(x_52);
lean::dec(x_48);
x_59 = !lean::is_exclusive(x_58);
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = lean::cnstr_get(x_58, 0);
x_61 = lean::nat_mod(x_60, x_54);
lean::dec(x_54);
lean::dec(x_60);
x_62 = lean::nat_add(x_4, x_61);
lean::dec(x_61);
lean::cnstr_set(x_58, 0, x_62);
return x_58;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_63 = lean::cnstr_get(x_58, 0);
x_64 = lean::cnstr_get(x_58, 1);
lean::inc(x_64);
lean::inc(x_63);
lean::dec(x_58);
x_65 = lean::nat_mod(x_63, x_54);
lean::dec(x_54);
lean::dec(x_63);
x_66 = lean::nat_add(x_4, x_65);
lean::dec(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_64);
return x_67;
}
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_68 = lean::cnstr_get(x_7, 0);
x_69 = lean::cnstr_get(x_7, 1);
lean::inc(x_69);
lean::inc(x_68);
lean::dec(x_7);
x_70 = lean::nat_sub(x_69, x_68);
lean::dec(x_69);
x_71 = lean::mk_nat_obj(1u);
x_72 = lean::nat_add(x_70, x_71);
lean::dec(x_70);
x_73 = lean::nat_sub(x_3, x_4);
x_74 = lean::nat_add(x_73, x_71);
lean::dec(x_73);
x_75 = lean::mk_nat_obj(1000u);
x_76 = lean::nat_mul(x_74, x_75);
x_77 = lean::mk_nat_obj(0u);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_2);
x_79 = l___private_init_data_random_1__randNatAux___main___rarg(x_1, x_68, x_72, x_76, x_78);
lean::dec(x_72);
lean::dec(x_68);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_79, 1);
lean::inc(x_81);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_82 = x_79;
} else {
 lean::dec_ref(x_79);
 x_82 = lean::box(0);
}
x_83 = lean::nat_mod(x_80, x_74);
lean::dec(x_74);
lean::dec(x_80);
x_84 = lean::nat_add(x_4, x_83);
lean::dec(x_83);
if (lean::is_scalar(x_82)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_82;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_81);
return x_85;
}
}
}
}
obj* l_randNat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_randNat___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_randNat___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_randNat___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_randBool___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::mk_nat_obj(1u);
x_5 = l_randNat___rarg(x_1, x_2, x_3, x_4);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::nat_dec_eq(x_7, x_4);
lean::dec(x_7);
x_9 = lean::box(x_8);
lean::cnstr_set(x_5, 0, x_9);
return x_5;
}
else
{
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_5);
x_12 = lean::nat_dec_eq(x_10, x_4);
lean::dec(x_10);
x_13 = lean::box(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
}
}
obj* l_randBool(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_randBool___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_IO_mkStdGenRef___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_mkStdGen(x_1);
return x_2;
}
}
obj* l_IO_mkStdGenRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_IO_mkStdGenRef___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_IO_setRandSeed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_mkStdGen(x_1);
x_4 = l_IO_stdGenRef;
x_5 = lean::io_ref_set(x_4, x_3, x_2);
return x_5;
}
}
obj* l_IO_setRandSeed___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_setRandSeed(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = l_stdNext___main(x_10);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = lean::nat_mul(x_9, x_2);
lean::dec(x_9);
x_15 = lean::nat_add(x_8, x_7);
lean::dec(x_8);
x_16 = lean::nat_div(x_15, x_2);
lean::dec(x_15);
x_17 = lean::nat_sub(x_16, x_7);
lean::dec(x_16);
x_18 = lean::nat_sub(x_13, x_1);
lean::dec(x_13);
x_19 = lean::nat_add(x_14, x_18);
lean::dec(x_18);
lean::dec(x_14);
lean::cnstr_set(x_11, 0, x_19);
x_3 = x_17;
x_4 = x_11;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_21 = lean::cnstr_get(x_11, 0);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_11);
x_23 = lean::nat_mul(x_9, x_2);
lean::dec(x_9);
x_24 = lean::nat_add(x_8, x_7);
lean::dec(x_8);
x_25 = lean::nat_div(x_24, x_2);
lean::dec(x_24);
x_26 = lean::nat_sub(x_25, x_7);
lean::dec(x_25);
x_27 = lean::nat_sub(x_21, x_1);
lean::dec(x_21);
x_28 = lean::nat_add(x_23, x_27);
lean::dec(x_27);
lean::dec(x_23);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
x_3 = x_26;
x_4 = x_29;
goto _start;
}
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
obj* l_randNat___at_IO_rand___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = l_stdRange;
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_9 = lean::nat_sub(x_8, x_7);
lean::dec(x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_12 = lean::nat_sub(x_3, x_2);
x_13 = lean::nat_add(x_12, x_10);
lean::dec(x_12);
x_14 = lean::mk_nat_obj(1000u);
x_15 = lean::nat_mul(x_13, x_14);
x_16 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 0, x_16);
x_17 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_7, x_11, x_15, x_5);
lean::dec(x_11);
lean::dec(x_7);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = lean::nat_mod(x_19, x_13);
lean::dec(x_13);
lean::dec(x_19);
x_21 = lean::nat_add(x_2, x_20);
lean::dec(x_20);
lean::cnstr_set(x_17, 0, x_21);
return x_17;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_17);
x_24 = lean::nat_mod(x_22, x_13);
lean::dec(x_13);
lean::dec(x_22);
x_25 = lean::nat_add(x_2, x_24);
lean::dec(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_27 = lean::cnstr_get(x_5, 0);
x_28 = lean::cnstr_get(x_5, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_5);
x_29 = lean::nat_sub(x_28, x_27);
lean::dec(x_28);
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_add(x_29, x_30);
lean::dec(x_29);
x_32 = lean::nat_sub(x_3, x_2);
x_33 = lean::nat_add(x_32, x_30);
lean::dec(x_32);
x_34 = lean::mk_nat_obj(1000u);
x_35 = lean::nat_mul(x_33, x_34);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_1);
x_38 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_27, x_31, x_35, x_37);
lean::dec(x_31);
lean::dec(x_27);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_41 = x_38;
} else {
 lean::dec_ref(x_38);
 x_41 = lean::box(0);
}
x_42 = lean::nat_mod(x_39, x_33);
lean::dec(x_33);
lean::dec(x_39);
x_43 = lean::nat_add(x_2, x_42);
lean::dec(x_42);
if (lean::is_scalar(x_41)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_41;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
return x_44;
}
}
else
{
obj* x_45; uint8 x_46; 
x_45 = l_stdRange;
x_46 = !lean::is_exclusive(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_47 = lean::cnstr_get(x_45, 0);
x_48 = lean::cnstr_get(x_45, 1);
x_49 = lean::nat_sub(x_48, x_47);
lean::dec(x_48);
x_50 = lean::mk_nat_obj(1u);
x_51 = lean::nat_add(x_49, x_50);
lean::dec(x_49);
x_52 = lean::nat_sub(x_2, x_3);
x_53 = lean::nat_add(x_52, x_50);
lean::dec(x_52);
x_54 = lean::mk_nat_obj(1000u);
x_55 = lean::nat_mul(x_53, x_54);
x_56 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 0, x_56);
x_57 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_47, x_51, x_55, x_45);
lean::dec(x_51);
lean::dec(x_47);
x_58 = !lean::is_exclusive(x_57);
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_61; 
x_59 = lean::cnstr_get(x_57, 0);
x_60 = lean::nat_mod(x_59, x_53);
lean::dec(x_53);
lean::dec(x_59);
x_61 = lean::nat_add(x_3, x_60);
lean::dec(x_60);
lean::cnstr_set(x_57, 0, x_61);
return x_57;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_57, 0);
x_63 = lean::cnstr_get(x_57, 1);
lean::inc(x_63);
lean::inc(x_62);
lean::dec(x_57);
x_64 = lean::nat_mod(x_62, x_53);
lean::dec(x_53);
lean::dec(x_62);
x_65 = lean::nat_add(x_3, x_64);
lean::dec(x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_63);
return x_66;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_67 = lean::cnstr_get(x_45, 0);
x_68 = lean::cnstr_get(x_45, 1);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_45);
x_69 = lean::nat_sub(x_68, x_67);
lean::dec(x_68);
x_70 = lean::mk_nat_obj(1u);
x_71 = lean::nat_add(x_69, x_70);
lean::dec(x_69);
x_72 = lean::nat_sub(x_2, x_3);
x_73 = lean::nat_add(x_72, x_70);
lean::dec(x_72);
x_74 = lean::mk_nat_obj(1000u);
x_75 = lean::nat_mul(x_73, x_74);
x_76 = lean::mk_nat_obj(0u);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_1);
x_78 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_67, x_71, x_75, x_77);
lean::dec(x_71);
lean::dec(x_67);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_78, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_81 = x_78;
} else {
 lean::dec_ref(x_78);
 x_81 = lean::box(0);
}
x_82 = lean::nat_mod(x_79, x_73);
lean::dec(x_73);
lean::dec(x_79);
x_83 = lean::nat_add(x_3, x_82);
lean::dec(x_82);
if (lean::is_scalar(x_81)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_81;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_80);
return x_84;
}
}
}
}
obj* l_IO_rand(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_IO_stdGenRef;
x_5 = lean::io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = l_randNat___at_IO_rand___spec__1(x_7, x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::io_ref_set(x_4, x_11, x_5);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_12, 0);
lean::dec(x_14);
lean::cnstr_set(x_12, 0, x_10);
return x_12;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8 x_17; 
lean::dec(x_10);
x_17 = !lean::is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_12, 0);
x_19 = lean::cnstr_get(x_12, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_12);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_5, 0);
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_5);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = l_randNat___at_IO_rand___spec__1(x_21, x_1, x_2);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
lean::dec(x_25);
x_28 = lean::io_ref_set(x_4, x_27, x_24);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_30 = x_28;
} else {
 lean::dec_ref(x_28);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_29);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_26);
x_32 = lean::cnstr_get(x_28, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_34 = x_28;
} else {
 lean::dec_ref(x_28);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_5);
if (x_36 == 0)
{
return x_5;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_5, 0);
x_38 = lean::cnstr_get(x_5, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_5);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
}
obj* l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_randNat___at_IO_rand___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_randNat___at_IO_rand___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_IO_rand___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_rand(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* initialize_init_io(obj*);
obj* initialize_init_data_int_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_random(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_int_default(w);
if (io_result_is_error(w)) return w;
l_stdRange = _init_l_stdRange();
lean::mark_persistent(l_stdRange);
l_stdNext___main___closed__1 = _init_l_stdNext___main___closed__1();
lean::mark_persistent(l_stdNext___main___closed__1);
l_stdNext___main___closed__2 = _init_l_stdNext___main___closed__2();
lean::mark_persistent(l_stdNext___main___closed__2);
l_stdNext___main___closed__3 = _init_l_stdNext___main___closed__3();
lean::mark_persistent(l_stdNext___main___closed__3);
l_stdNext___main___closed__4 = _init_l_stdNext___main___closed__4();
lean::mark_persistent(l_stdNext___main___closed__4);
l_stdNext___main___closed__5 = _init_l_stdNext___main___closed__5();
lean::mark_persistent(l_stdNext___main___closed__5);
l_stdNext___main___closed__6 = _init_l_stdNext___main___closed__6();
lean::mark_persistent(l_stdNext___main___closed__6);
l_stdNext___main___closed__7 = _init_l_stdNext___main___closed__7();
lean::mark_persistent(l_stdNext___main___closed__7);
l_stdNext___main___closed__8 = _init_l_stdNext___main___closed__8();
lean::mark_persistent(l_stdNext___main___closed__8);
l_stdNext___main___closed__9 = _init_l_stdNext___main___closed__9();
lean::mark_persistent(l_stdNext___main___closed__9);
l_StdGen_RandomGen = _init_l_StdGen_RandomGen();
lean::mark_persistent(l_StdGen_RandomGen);
l_IO_mkStdGenRef___closed__1 = _init_l_IO_mkStdGenRef___closed__1();
lean::mark_persistent(l_IO_mkStdGenRef___closed__1);
w = l_IO_mkStdGenRef(w);
if (io_result_is_error(w)) return w;
l_IO_stdGenRef = io_result_get_value(w);
lean::mark_persistent(l_IO_stdGenRef);
return w;
}
