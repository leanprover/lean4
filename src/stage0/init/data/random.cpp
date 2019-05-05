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
obj* l_randBool___boxed(obj*);
obj* l___private_init_data_random_1__randNatAux___boxed(obj*);
obj* l___private_init_data_random_1__randNatAux___rarg(obj*, obj*, obj*, obj*, obj*);
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
obj* l_IO_stdGenRef;
extern obj* l_Sigma_HasRepr___rarg___closed__2;
obj* l_randNat___boxed(obj*);
obj* l_mkStdGen___boxed(obj*);
obj* l___private_init_data_random_1__randNatAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_rand(obj*, obj*, obj*);
obj* l_stdSplit___main(obj*);
namespace lean {
obj* int_mul(obj*, obj*);
}
obj* l___private_init_data_random_1__randNatAux___main(obj*);
extern obj* l_Int_zero;
obj* l_IO_mkStdGenRef(obj*);
obj* l_randNat___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_data_random_1__randNatAux___main___boxed(obj*);
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
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1ul);
x_1 = lean::mk_nat_obj(2147483562ul);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_StdGen_HasRepr(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Nat_repr(x_1);
x_7 = l_Sigma_HasRepr___rarg___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = l_List_reprAux___main___rarg___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean::string_append(x_11, x_12);
lean::dec(x_12);
x_15 = l_Sigma_HasRepr___rarg___closed__2;
x_16 = lean::string_append(x_13, x_15);
return x_16;
}
}
obj* _init_l_stdNext___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_0);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_4);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_0);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_8);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_0);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_0);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_22);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_24);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_0);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_28);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_30);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_32);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_0);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_36);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_38);
lean::dec(x_38);
return x_40;
}
}
obj* _init_l_stdNext___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_1);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_0);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_0);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_0);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_0);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_24);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_26);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_28);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_0);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_32);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_0);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_36);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_0);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_40);
lean::dec(x_40);
return x_42;
}
}
obj* _init_l_stdNext___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_1);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_0);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_4);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_0);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_8);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_0);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_0);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_0);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_22);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_0);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_26);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_0);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_30);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_32);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_34);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_0);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_38);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_0);
lean::dec(x_40);
return x_42;
}
}
obj* _init_l_stdNext___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_0);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_4);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_0);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_0);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_0);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_22);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_24);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_0);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_28);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_30);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_32);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_0);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_36);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_0);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_40);
lean::dec(x_40);
return x_42;
}
}
obj* _init_l_stdNext___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_1);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_0);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_0);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_0);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_0);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_0);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_24);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_0);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_28);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_0);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_32);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_0);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_36);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_38);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_0);
lean::dec(x_40);
x_44 = lean::int_add(x_42, x_42);
lean::dec(x_42);
x_46 = lean::int_add(x_44, x_44);
lean::dec(x_44);
return x_46;
}
}
obj* _init_l_stdNext___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_0);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_0);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_8);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_0);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_12);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_0);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_16);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_20);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_0);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_24);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_0);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_28);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_0);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_32);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_0);
lean::dec(x_34);
return x_36;
}
}
obj* _init_l_stdNext___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_92; obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_0);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_0);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_0);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_0);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_0);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_0);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_22);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_0);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_26);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_0);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_30);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_0);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_34);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_0);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_38);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_0);
lean::dec(x_40);
x_44 = lean::int_add(x_42, x_42);
lean::dec(x_42);
x_46 = lean::int_add(x_44, x_0);
lean::dec(x_44);
x_48 = lean::int_add(x_46, x_46);
lean::dec(x_46);
x_50 = lean::int_add(x_48, x_0);
lean::dec(x_48);
x_52 = lean::int_add(x_50, x_50);
lean::dec(x_50);
x_54 = lean::int_add(x_52, x_0);
lean::dec(x_52);
x_56 = lean::int_add(x_54, x_54);
lean::dec(x_54);
x_58 = lean::int_add(x_56, x_0);
lean::dec(x_56);
x_60 = lean::int_add(x_58, x_58);
lean::dec(x_58);
x_62 = lean::int_add(x_60, x_0);
lean::dec(x_60);
x_64 = lean::int_add(x_62, x_62);
lean::dec(x_62);
x_66 = lean::int_add(x_64, x_0);
lean::dec(x_64);
x_68 = lean::int_add(x_66, x_66);
lean::dec(x_66);
x_70 = lean::int_add(x_68, x_0);
lean::dec(x_68);
x_72 = lean::int_add(x_70, x_70);
lean::dec(x_70);
x_74 = lean::int_add(x_72, x_0);
lean::dec(x_72);
x_76 = lean::int_add(x_74, x_74);
lean::dec(x_74);
x_78 = lean::int_add(x_76, x_0);
lean::dec(x_76);
x_80 = lean::int_add(x_78, x_78);
lean::dec(x_78);
x_82 = lean::int_add(x_80, x_0);
lean::dec(x_80);
x_84 = lean::int_add(x_82, x_82);
lean::dec(x_82);
x_86 = lean::int_add(x_84, x_0);
lean::dec(x_84);
x_88 = lean::int_add(x_86, x_86);
lean::dec(x_86);
x_90 = lean::int_add(x_88, x_0);
lean::dec(x_88);
x_92 = lean::int_add(x_90, x_90);
lean::dec(x_90);
x_94 = lean::int_add(x_92, x_92);
lean::dec(x_92);
x_96 = lean::int_add(x_94, x_0);
lean::dec(x_94);
x_98 = lean::int_add(x_96, x_96);
lean::dec(x_96);
x_100 = lean::int_add(x_98, x_98);
lean::dec(x_98);
x_102 = lean::int_add(x_100, x_0);
lean::dec(x_100);
x_104 = lean::int_add(x_102, x_102);
lean::dec(x_102);
x_106 = lean::int_add(x_104, x_104);
lean::dec(x_104);
x_108 = lean::int_add(x_106, x_0);
lean::dec(x_106);
x_110 = lean::int_add(x_108, x_108);
lean::dec(x_108);
return x_110;
}
}
obj* _init_l_stdNext___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_92; obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_0);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_0);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_0);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_0);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_0);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_0);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_22);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_0);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_26);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_0);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_30);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_0);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_34);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_0);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_38);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_0);
lean::dec(x_40);
x_44 = lean::int_add(x_42, x_42);
lean::dec(x_42);
x_46 = lean::int_add(x_44, x_0);
lean::dec(x_44);
x_48 = lean::int_add(x_46, x_46);
lean::dec(x_46);
x_50 = lean::int_add(x_48, x_0);
lean::dec(x_48);
x_52 = lean::int_add(x_50, x_50);
lean::dec(x_50);
x_54 = lean::int_add(x_52, x_0);
lean::dec(x_52);
x_56 = lean::int_add(x_54, x_54);
lean::dec(x_54);
x_58 = lean::int_add(x_56, x_0);
lean::dec(x_56);
x_60 = lean::int_add(x_58, x_58);
lean::dec(x_58);
x_62 = lean::int_add(x_60, x_0);
lean::dec(x_60);
x_64 = lean::int_add(x_62, x_62);
lean::dec(x_62);
x_66 = lean::int_add(x_64, x_0);
lean::dec(x_64);
x_68 = lean::int_add(x_66, x_66);
lean::dec(x_66);
x_70 = lean::int_add(x_68, x_0);
lean::dec(x_68);
x_72 = lean::int_add(x_70, x_70);
lean::dec(x_70);
x_74 = lean::int_add(x_72, x_0);
lean::dec(x_72);
x_76 = lean::int_add(x_74, x_74);
lean::dec(x_74);
x_78 = lean::int_add(x_76, x_0);
lean::dec(x_76);
x_80 = lean::int_add(x_78, x_78);
lean::dec(x_78);
x_82 = lean::int_add(x_80, x_0);
lean::dec(x_80);
x_84 = lean::int_add(x_82, x_82);
lean::dec(x_82);
x_86 = lean::int_add(x_84, x_0);
lean::dec(x_84);
x_88 = lean::int_add(x_86, x_86);
lean::dec(x_86);
x_90 = lean::int_add(x_88, x_88);
lean::dec(x_88);
x_92 = lean::int_add(x_90, x_90);
lean::dec(x_90);
x_94 = lean::int_add(x_92, x_92);
lean::dec(x_92);
x_96 = lean::int_add(x_94, x_94);
lean::dec(x_94);
x_98 = lean::int_add(x_96, x_96);
lean::dec(x_96);
x_100 = lean::int_add(x_98, x_0);
lean::dec(x_98);
x_102 = lean::int_add(x_100, x_100);
lean::dec(x_100);
x_104 = lean::int_add(x_102, x_0);
lean::dec(x_102);
x_106 = lean::int_add(x_104, x_104);
lean::dec(x_104);
x_108 = lean::int_add(x_106, x_0);
lean::dec(x_106);
return x_108;
}
}
obj* _init_l_stdNext___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_92; obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; 
x_0 = l_Int_one;
x_1 = lean::int_add(x_0, x_0);
x_2 = lean::int_add(x_1, x_0);
lean::dec(x_1);
x_4 = lean::int_add(x_2, x_2);
lean::dec(x_2);
x_6 = lean::int_add(x_4, x_0);
lean::dec(x_4);
x_8 = lean::int_add(x_6, x_6);
lean::dec(x_6);
x_10 = lean::int_add(x_8, x_0);
lean::dec(x_8);
x_12 = lean::int_add(x_10, x_10);
lean::dec(x_10);
x_14 = lean::int_add(x_12, x_0);
lean::dec(x_12);
x_16 = lean::int_add(x_14, x_14);
lean::dec(x_14);
x_18 = lean::int_add(x_16, x_0);
lean::dec(x_16);
x_20 = lean::int_add(x_18, x_18);
lean::dec(x_18);
x_22 = lean::int_add(x_20, x_0);
lean::dec(x_20);
x_24 = lean::int_add(x_22, x_22);
lean::dec(x_22);
x_26 = lean::int_add(x_24, x_0);
lean::dec(x_24);
x_28 = lean::int_add(x_26, x_26);
lean::dec(x_26);
x_30 = lean::int_add(x_28, x_0);
lean::dec(x_28);
x_32 = lean::int_add(x_30, x_30);
lean::dec(x_30);
x_34 = lean::int_add(x_32, x_0);
lean::dec(x_32);
x_36 = lean::int_add(x_34, x_34);
lean::dec(x_34);
x_38 = lean::int_add(x_36, x_0);
lean::dec(x_36);
x_40 = lean::int_add(x_38, x_38);
lean::dec(x_38);
x_42 = lean::int_add(x_40, x_0);
lean::dec(x_40);
x_44 = lean::int_add(x_42, x_42);
lean::dec(x_42);
x_46 = lean::int_add(x_44, x_0);
lean::dec(x_44);
x_48 = lean::int_add(x_46, x_46);
lean::dec(x_46);
x_50 = lean::int_add(x_48, x_0);
lean::dec(x_48);
x_52 = lean::int_add(x_50, x_50);
lean::dec(x_50);
x_54 = lean::int_add(x_52, x_0);
lean::dec(x_52);
x_56 = lean::int_add(x_54, x_54);
lean::dec(x_54);
x_58 = lean::int_add(x_56, x_0);
lean::dec(x_56);
x_60 = lean::int_add(x_58, x_58);
lean::dec(x_58);
x_62 = lean::int_add(x_60, x_0);
lean::dec(x_60);
x_64 = lean::int_add(x_62, x_62);
lean::dec(x_62);
x_66 = lean::int_add(x_64, x_0);
lean::dec(x_64);
x_68 = lean::int_add(x_66, x_66);
lean::dec(x_66);
x_70 = lean::int_add(x_68, x_0);
lean::dec(x_68);
x_72 = lean::int_add(x_70, x_70);
lean::dec(x_70);
x_74 = lean::int_add(x_72, x_0);
lean::dec(x_72);
x_76 = lean::int_add(x_74, x_74);
lean::dec(x_74);
x_78 = lean::int_add(x_76, x_0);
lean::dec(x_76);
x_80 = lean::int_add(x_78, x_78);
lean::dec(x_78);
x_82 = lean::int_add(x_80, x_0);
lean::dec(x_80);
x_84 = lean::int_add(x_82, x_82);
lean::dec(x_82);
x_86 = lean::int_add(x_84, x_0);
lean::dec(x_84);
x_88 = lean::int_add(x_86, x_86);
lean::dec(x_86);
x_90 = lean::int_add(x_88, x_0);
lean::dec(x_88);
x_92 = lean::int_add(x_90, x_90);
lean::dec(x_90);
x_94 = lean::int_add(x_92, x_92);
lean::dec(x_92);
x_96 = lean::int_add(x_94, x_0);
lean::dec(x_94);
x_98 = lean::int_add(x_96, x_96);
lean::dec(x_96);
x_100 = lean::int_add(x_98, x_98);
lean::dec(x_98);
x_102 = lean::int_add(x_100, x_0);
lean::dec(x_100);
x_104 = lean::int_add(x_102, x_102);
lean::dec(x_102);
x_106 = lean::int_add(x_104, x_104);
lean::dec(x_104);
x_108 = lean::int_add(x_106, x_0);
lean::dec(x_106);
x_110 = lean::int_add(x_108, x_108);
lean::dec(x_108);
x_112 = lean::int_add(x_110, x_0);
lean::dec(x_110);
return x_112;
}
}
obj* l_stdNext___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_37; uint8 x_40; obj* x_41; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_5 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = lean::nat2int(x_1);
x_7 = l_stdNext___main___closed__1;
x_8 = lean::int_div(x_6, x_7);
x_9 = lean::int_mul(x_8, x_7);
x_10 = lean::int_sub(x_6, x_9);
lean::dec(x_9);
lean::dec(x_6);
x_13 = l_stdNext___main___closed__2;
x_14 = lean::int_mul(x_13, x_10);
lean::dec(x_10);
x_16 = l_stdNext___main___closed__3;
x_17 = lean::int_mul(x_8, x_16);
lean::dec(x_8);
x_19 = lean::int_sub(x_14, x_17);
lean::dec(x_17);
lean::dec(x_14);
x_22 = l_Int_zero;
x_23 = lean::int_dec_lt(x_19, x_22);
x_24 = lean::nat2int(x_3);
x_25 = l_stdNext___main___closed__4;
x_26 = lean::int_div(x_24, x_25);
x_27 = lean::int_mul(x_26, x_25);
x_28 = lean::int_sub(x_24, x_27);
lean::dec(x_27);
lean::dec(x_24);
x_31 = l_stdNext___main___closed__5;
x_32 = lean::int_mul(x_31, x_28);
lean::dec(x_28);
x_34 = l_stdNext___main___closed__6;
x_35 = lean::int_mul(x_26, x_34);
lean::dec(x_26);
x_37 = lean::int_sub(x_32, x_35);
lean::dec(x_35);
lean::dec(x_32);
x_40 = lean::int_dec_lt(x_37, x_22);
if (x_23 == 0)
{
x_41 = x_19;
goto lbl_42;
}
else
{
obj* x_43; obj* x_44; 
x_43 = l_stdNext___main___closed__9;
x_44 = lean::int_add(x_19, x_43);
lean::dec(x_19);
x_41 = x_44;
goto lbl_42;
}
lbl_42:
{
obj* x_46; obj* x_47; 
x_46 = l_Int_toNat___main(x_41);
if (x_40 == 0)
{
x_47 = x_37;
goto lbl_48;
}
else
{
obj* x_49; obj* x_50; 
x_49 = l_stdNext___main___closed__8;
x_50 = lean::int_add(x_37, x_49);
lean::dec(x_37);
x_47 = x_50;
goto lbl_48;
}
lbl_48:
{
obj* x_52; obj* x_54; uint8 x_55; obj* x_56; obj* x_58; 
x_52 = lean::int_sub(x_41, x_47);
lean::dec(x_41);
x_54 = l_Int_one;
x_55 = lean::int_dec_lt(x_52, x_54);
x_56 = l_Int_toNat___main(x_47);
lean::dec(x_47);
if (lean::is_scalar(x_5)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_5;
}
lean::cnstr_set(x_58, 0, x_46);
lean::cnstr_set(x_58, 1, x_56);
if (x_55 == 0)
{
obj* x_59; obj* x_60; obj* x_62; obj* x_64; 
x_59 = l_stdNext___main___closed__7;
x_60 = lean::int_mod(x_52, x_59);
lean::dec(x_52);
x_62 = l_Int_toNat___main(x_60);
lean::dec(x_60);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_58);
return x_64;
}
else
{
obj* x_65; obj* x_66; obj* x_68; obj* x_70; 
x_65 = l_stdNext___main___closed__7;
x_66 = lean::int_add(x_52, x_65);
lean::dec(x_52);
x_68 = l_Int_toNat___main(x_66);
lean::dec(x_66);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_58);
return x_70;
}
}
}
}
}
obj* l_stdNext(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_stdNext___main(x_0);
return x_1;
}
}
obj* l_stdSplit___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; uint8 x_6; obj* x_7; uint8 x_8; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::mk_nat_obj(2147483562ul);
x_6 = lean::nat_dec_eq(x_1, x_5);
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_dec_eq(x_3, x_7);
lean::inc(x_0);
x_10 = l_stdNext___main(x_0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
if (x_6 == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
x_15 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::nat_add(x_1, x_7);
lean::dec(x_1);
if (lean::is_scalar(x_19)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_19;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_17);
if (x_8 == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
x_23 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
if (lean::is_scalar(x_11)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_11;
}
lean::cnstr_set(x_25, 0, x_15);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_3);
x_28 = lean::mk_nat_obj(2147483398ul);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_22);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
else
{
obj* x_32; obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_12, 0);
x_34 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_36 = x_12;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_12);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_7);
lean::cnstr_set(x_37, 1, x_34);
if (x_8 == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
x_38 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
if (lean::is_scalar(x_11)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_11;
}
lean::cnstr_set(x_40, 0, x_32);
lean::cnstr_set(x_40, 1, x_38);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_37);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_3);
x_43 = lean::mk_nat_obj(2147483398ul);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_32);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_37);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
}
}
obj* l_stdSplit(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_stdSplit___main(x_0);
return x_1;
}
}
obj* l_StdGen_RandomGen___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_stdRange;
return x_1;
}
}
obj* _init_l_StdGen_RandomGen() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_StdGen_RandomGen___lambda__1___boxed), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_stdNext), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_stdSplit), 1, 0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_StdGen_RandomGen___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_StdGen_RandomGen___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_mkStdGen(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_1 = lean::mk_nat_obj(2147483562ul);
x_2 = lean::nat_div(x_0, x_1);
x_3 = lean::nat_mod(x_0, x_1);
x_4 = lean::mk_nat_obj(2147483398ul);
x_5 = lean::nat_mod(x_2, x_4);
lean::dec(x_2);
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_add(x_3, x_7);
lean::dec(x_3);
x_10 = lean::nat_add(x_5, x_7);
lean::dec(x_5);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
obj* l_mkStdGen___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkStdGen(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_random_1__randNatAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_36; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_12);
x_18 = lean::cnstr_get(x_17, 0);
x_20 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_22 = x_17;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
x_23 = lean::nat_mul(x_10, x_2);
lean::dec(x_10);
x_25 = lean::nat_add(x_8, x_7);
lean::dec(x_8);
x_27 = lean::nat_div(x_25, x_2);
lean::dec(x_25);
x_29 = lean::nat_sub(x_27, x_7);
lean::dec(x_27);
x_31 = lean::nat_sub(x_18, x_1);
lean::dec(x_18);
x_33 = lean::nat_add(x_23, x_31);
lean::dec(x_31);
lean::dec(x_23);
if (lean::is_scalar(x_22)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_22;
}
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_20);
x_3 = x_29;
x_4 = x_36;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
}
}
obj* l___private_init_data_random_1__randNatAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_random_1__randNatAux___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l___private_init_data_random_1__randNatAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_random_1__randNatAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_data_random_1__randNatAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_random_1__randNatAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_random_1__randNatAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_random_1__randNatAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_random_1__randNatAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_random_1__randNatAux___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l___private_init_data_random_1__randNatAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_random_1__randNatAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_data_random_1__randNatAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_random_1__randNatAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_randNat___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; obj* x_8; 
x_4 = lean::nat_dec_lt(x_3, x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::inc(x_1);
x_8 = lean::apply_1(x_5, x_1);
if (x_4 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_37; obj* x_39; 
x_9 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_13 = x_8;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::nat_sub(x_11, x_9);
lean::dec(x_11);
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_14, x_16);
lean::dec(x_14);
x_19 = lean::nat_sub(x_3, x_2);
x_20 = lean::nat_add(x_19, x_16);
lean::dec(x_19);
x_22 = lean::mk_nat_obj(1000ul);
x_23 = lean::nat_mul(x_20, x_22);
x_24 = lean::mk_nat_obj(0ul);
if (lean::is_scalar(x_13)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_13;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_1);
x_26 = l___private_init_data_random_1__randNatAux___main___rarg(x_0, x_9, x_17, x_23, x_25);
lean::dec(x_17);
lean::dec(x_9);
x_29 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_33 = x_26;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_26);
 x_33 = lean::box(0);
}
x_34 = lean::nat_mod(x_29, x_20);
lean::dec(x_20);
lean::dec(x_29);
x_37 = lean::nat_add(x_2, x_34);
lean::dec(x_34);
if (lean::is_scalar(x_33)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_33;
}
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_31);
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_68; obj* x_70; 
x_40 = lean::cnstr_get(x_8, 0);
x_42 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_44 = x_8;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_8);
 x_44 = lean::box(0);
}
x_45 = lean::nat_sub(x_42, x_40);
lean::dec(x_42);
x_47 = lean::mk_nat_obj(1ul);
x_48 = lean::nat_add(x_45, x_47);
lean::dec(x_45);
x_50 = lean::nat_sub(x_2, x_3);
x_51 = lean::nat_add(x_50, x_47);
lean::dec(x_50);
x_53 = lean::mk_nat_obj(1000ul);
x_54 = lean::nat_mul(x_51, x_53);
x_55 = lean::mk_nat_obj(0ul);
if (lean::is_scalar(x_44)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_44;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_1);
x_57 = l___private_init_data_random_1__randNatAux___main___rarg(x_0, x_40, x_48, x_54, x_56);
lean::dec(x_48);
lean::dec(x_40);
x_60 = lean::cnstr_get(x_57, 0);
x_62 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_64 = x_57;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
x_65 = lean::nat_mod(x_60, x_51);
lean::dec(x_51);
lean::dec(x_60);
x_68 = lean::nat_add(x_3, x_65);
lean::dec(x_65);
if (lean::is_scalar(x_64)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_64;
}
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_62);
return x_70;
}
}
}
obj* l_randNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_randNat___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_randNat___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_randNat___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_randNat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_randNat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_randBool___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::mk_nat_obj(1ul);
x_4 = l_randNat___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::nat_dec_eq(x_5, x_3);
lean::dec(x_5);
x_12 = lean::box(x_10);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
obj* l_randBool(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_randBool___rarg), 2, 0);
return x_1;
}
}
obj* l_randBool___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_randBool(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_IO_mkStdGenRef___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = l_mkStdGen(x_0);
return x_1;
}
}
obj* l_IO_mkStdGenRef(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_IO_mkStdGenRef___closed__1;
x_2 = lean::io_mk_ref(x_1, x_0);
return x_2;
}
}
obj* l_IO_setRandSeed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_mkStdGen(x_0);
x_3 = l_IO_stdGenRef;
x_4 = lean::io_ref_set(x_3, x_2, x_1);
return x_4;
}
}
obj* l_IO_setRandSeed___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_setRandSeed(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::dec(x_3);
x_14 = l_stdNext___main(x_11);
x_15 = lean::cnstr_get(x_14, 0);
x_17 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_19 = x_14;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = lean::nat_mul(x_9, x_1);
lean::dec(x_9);
x_22 = lean::nat_add(x_7, x_6);
lean::dec(x_7);
x_24 = lean::nat_div(x_22, x_1);
lean::dec(x_22);
x_26 = lean::nat_sub(x_24, x_6);
lean::dec(x_24);
x_28 = lean::nat_sub(x_15, x_0);
lean::dec(x_15);
x_30 = lean::nat_add(x_20, x_28);
lean::dec(x_28);
lean::dec(x_20);
if (lean::is_scalar(x_19)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_19;
}
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set(x_33, 1, x_17);
x_2 = x_26;
x_3 = x_33;
goto _start;
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_randNat___at_IO_rand___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_33; obj* x_35; 
x_4 = l_stdRange;
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::nat_sub(x_7, x_5);
lean::dec(x_7);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_10, x_12);
lean::dec(x_10);
x_15 = lean::nat_sub(x_2, x_1);
x_16 = lean::nat_add(x_15, x_12);
lean::dec(x_15);
x_18 = lean::mk_nat_obj(1000ul);
x_19 = lean::nat_mul(x_16, x_18);
x_20 = lean::mk_nat_obj(0ul);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_0);
x_22 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_5, x_13, x_19, x_21);
lean::dec(x_13);
lean::dec(x_5);
x_25 = lean::cnstr_get(x_22, 0);
x_27 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
x_30 = lean::nat_mod(x_25, x_16);
lean::dec(x_16);
lean::dec(x_25);
x_33 = lean::nat_add(x_1, x_30);
lean::dec(x_30);
if (lean::is_scalar(x_29)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_29;
}
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_27);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_65; obj* x_67; 
x_36 = l_stdRange;
x_37 = lean::cnstr_get(x_36, 0);
x_39 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_36);
 x_41 = lean::box(0);
}
x_42 = lean::nat_sub(x_39, x_37);
lean::dec(x_39);
x_44 = lean::mk_nat_obj(1ul);
x_45 = lean::nat_add(x_42, x_44);
lean::dec(x_42);
x_47 = lean::nat_sub(x_1, x_2);
x_48 = lean::nat_add(x_47, x_44);
lean::dec(x_47);
x_50 = lean::mk_nat_obj(1000ul);
x_51 = lean::nat_mul(x_48, x_50);
x_52 = lean::mk_nat_obj(0ul);
if (lean::is_scalar(x_41)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_41;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_0);
x_54 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_37, x_45, x_51, x_53);
lean::dec(x_45);
lean::dec(x_37);
x_57 = lean::cnstr_get(x_54, 0);
x_59 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_61 = x_54;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_54);
 x_61 = lean::box(0);
}
x_62 = lean::nat_mod(x_57, x_48);
lean::dec(x_48);
lean::dec(x_57);
x_65 = lean::nat_add(x_2, x_62);
lean::dec(x_62);
if (lean::is_scalar(x_61)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_61;
}
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_59);
return x_67;
}
}
}
obj* l_IO_rand(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_IO_stdGenRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_18; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
x_12 = l_randNat___at_IO_rand___spec__1(x_5, x_0, x_1);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::io_ref_set(x_3, x_15, x_11);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_21 = x_18;
} else {
 lean::inc(x_19);
 lean::dec(x_18);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_13);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_18, 0);
x_26 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 x_28 = x_18;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_18);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
x_30 = lean::cnstr_get(x_4, 0);
x_32 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_34 = x_4;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_4);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
}
obj* l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_random_1__randNatAux___main___at_IO_rand___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_randNat___at_IO_rand___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_randNat___at_IO_rand___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_IO_rand___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_rand(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
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
