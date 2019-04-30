// Lean compiler output
// Module: init.lean.level
// Imports: init.data.option.basic init.lean.name init.lean.format
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
obj* l_Lean_LevelToFormat_levelHasToString;
obj* l_Lean_LevelToFormat_Result_succ___main(obj*);
obj* l_Lean_Level_toOffset___main(obj*);
obj* l_Lean_Level_hasParam___main___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_Level_instantiate(obj*, obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l_Lean_LevelToFormat_parenIfFalse(obj*, uint8);
obj* l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__3;
obj* l_Lean_LevelToFormat_Result_max(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__2;
obj* l_Lean_LevelToFormat_Level_toResult(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_format___main(obj*, uint8);
obj* l___private_init_lean_level_1__formatLst(obj*, obj*);
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__1;
obj* l_Lean_Level_ofNat(obj*);
obj* l_Lean_Level_toNat___main(obj*);
obj* l_Lean_Level_instantiate___main(obj*, obj*);
obj* l_Lean_Level_hasMvar___main___boxed(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Level_one;
obj* l_Lean_Level_hasParam___boxed(obj*);
obj* l_Lean_LevelToFormat_Level_format(obj*);
obj* l_Lean_LevelToFormat_parenIfFalse___boxed(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_succ(obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l___private_init_lean_level_1__formatLst___main(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_imax___main(obj*, obj*);
obj* l_Lean_Level_toOffset(obj*);
obj* l_Lean_Level_ofNat___boxed(obj*);
obj* l_Lean_fmt___at_Lean_LevelToFormat_Level_toResult___main___spec__1(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_Lean_Format_paren___closed__3;
obj* l_Lean_Level_toNat(obj*);
obj* l_Lean_Nat_imax(obj*, obj*);
obj* l_Lean_LevelToFormat_Level_toResult___main___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Lean_Level_hasParam(obj*);
obj* l_Lean_Level_toNat___boxed(obj*);
obj* l_Lean_fmt___at_Lean_LevelToFormat_Result_format___main___spec__1(obj*);
uint8 l_Lean_Level_hasParam___main(obj*);
obj* l_Lean_LevelToFormat_Result_format___main___boxed(obj*, obj*);
obj* l_Lean_LevelToFormat_parenIfFalse___main___boxed(obj*, obj*);
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_Lean_HasRepr___lambda__1(obj*);
obj* l_Lean_Level_ofNat___main___boxed(obj*);
obj* l_Lean_Level_toNat___main___boxed(obj*);
extern "C" usize lean_level_hash(obj*);
obj* l_Lean_Nat_imax___boxed(obj*, obj*);
obj* l_Lean_LevelToFormat_parenIfFalse___main(obj*, uint8);
obj* l_Lean_LevelToFormat_Level_toResult___main(obj*);
extern "C" obj* level_mk_succ(obj*);
obj* l_Lean_LevelToFormat_Result_format___boxed(obj*, obj*);
obj* l_Lean_Level_toNat___main___closed__1;
obj* l_Lean_LevelToFormat_Result_imax(obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_LevelToFormat_levelHasFormat;
obj* l_Lean_LevelToFormat_Result_format(obj*, uint8);
obj* l_Lean_Level_hasMvar___boxed(obj*);
obj* l_Nat_max(obj*, obj*);
uint8 l_Lean_Level_hasMvar___main(obj*);
obj* l_Lean_LevelToFormat_Result_max___main(obj*, obj*);
obj* l_Lean_Level_hash___boxed(obj*);
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_Lean_levelIsInhabited;
uint8 l_Lean_Level_hasMvar(obj*);
obj* _init_l_Lean_levelIsInhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_Level_one() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = level_mk_succ(x_0);
return x_1;
}
}
uint8 l_Lean_Level_hasParam___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
x_0 = x_1;
goto _start;
}
case 2:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = l_Lean_Level_hasParam___main(x_3);
if (x_5 == 0)
{
x_0 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
case 3:
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_10 = l_Lean_Level_hasParam___main(x_8);
if (x_10 == 0)
{
x_0 = x_9;
goto _start;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
case 4:
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
default:
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
}
}
}
obj* l_Lean_Level_hasParam___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Level_hasParam___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_Level_hasParam(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_Level_hasParam___main(x_0);
return x_1;
}
}
obj* l_Lean_Level_hasParam___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Level_hasParam(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_Level_hasMvar___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; uint8 x_2; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = l_Lean_Level_hasParam___main(x_1);
return x_2;
}
case 2:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = l_Lean_Level_hasParam___main(x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_Lean_Level_hasParam___main(x_4);
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
case 3:
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_10 = l_Lean_Level_hasParam___main(x_8);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = l_Lean_Level_hasParam___main(x_9);
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
case 5:
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
default:
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
}
}
}
obj* l_Lean_Level_hasMvar___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Level_hasMvar___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_Level_hasMvar(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_Level_hasMvar___main(x_0);
return x_1;
}
}
obj* l_Lean_Level_hasMvar___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Level_hasMvar(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Level_ofNat___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; 
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_sub(x_0, x_3);
x_5 = l_Lean_Level_ofNat___main(x_4);
lean::dec(x_4);
x_7 = level_mk_succ(x_5);
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::box(0);
return x_8;
}
}
}
obj* l_Lean_Level_ofNat___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_ofNat___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Level_ofNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_ofNat___main(x_0);
return x_1;
}
}
obj* l_Lean_Level_ofNat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_ofNat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Nat_imax(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Nat_max(x_0, x_1);
return x_4;
}
else
{
return x_2;
}
}
}
obj* l_Lean_Nat_imax___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Nat_imax(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Level_toNat___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Level_toNat___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = l_Lean_Level_toNat___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = l_Lean_Level_toNat___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_add(x_5, x_8);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_9);
return x_11;
}
}
case 2:
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_0, 0);
x_13 = lean::cnstr_get(x_0, 1);
x_14 = l_Lean_Level_toNat___main(x_12);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; 
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_19 = l_Lean_Level_toNat___main(x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_21; 
lean::dec(x_16);
x_21 = lean::box(0);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_28; 
x_22 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_24 = x_19;
} else {
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = l_Nat_max(x_16, x_22);
lean::dec(x_22);
lean::dec(x_16);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
}
}
case 3:
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_31 = l_Lean_Level_toNat___main(x_29);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_36; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_36 = l_Lean_Level_toNat___main(x_30);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; 
lean::dec(x_33);
x_38 = lean::box(0);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_45; 
x_39 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_39);
 lean::dec(x_36);
 x_41 = lean::box(0);
}
x_42 = l_Lean_Nat_imax(x_33, x_39);
lean::dec(x_39);
lean::dec(x_33);
if (lean::is_scalar(x_41)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_41;
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
}
}
default:
{
obj* x_46; 
x_46 = lean::box(0);
return x_46;
}
}
}
}
obj* l_Lean_Level_toNat___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_toNat___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Level_toNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_toNat___main(x_0);
return x_1;
}
}
obj* l_Lean_Level_toNat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_toNat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Level_toOffset___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_Level_toOffset___main(x_1);
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
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_7, x_10);
lean::dec(x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
default:
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(0ul);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_Lean_Level_toOffset(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_toOffset___main(x_0);
return x_1;
}
}
obj* l_Lean_Level_instantiate___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_Lean_Level_instantiate___main(x_0, x_2);
x_6 = level_mk_succ(x_5);
return x_6;
}
case 2:
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = l_Lean_Level_instantiate___main(x_0, x_7);
x_14 = l_Lean_Level_instantiate___main(x_0, x_9);
x_15 = level_mk_max(x_13, x_14);
return x_15;
}
case 3:
{
obj* x_16; obj* x_18; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
lean::inc(x_0);
x_22 = l_Lean_Level_instantiate___main(x_0, x_16);
x_23 = l_Lean_Level_instantiate___main(x_0, x_18);
x_24 = level_mk_imax(x_22, x_23);
return x_24;
}
case 4:
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_0, x_25);
if (lean::obj_tag(x_27) == 0)
{
return x_1;
}
else
{
obj* x_29; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_27, 0);
lean::inc(x_29);
lean::dec(x_27);
return x_29;
}
}
default:
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_Lean_Level_instantiate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_instantiate___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Level_hash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean_level_hash(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_LevelToFormat_Result_succ___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_1, x_4);
lean::dec(x_1);
if (lean::is_scalar(x_3)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_3;
}
lean::cnstr_set(x_7, 0, x_5);
return x_7;
}
case 2:
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_10, x_13);
lean::dec(x_10);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(2, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
default:
{
obj* x_17; obj* x_18; 
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_Lean_LevelToFormat_Result_succ(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_LevelToFormat_Result_succ___main(x_0);
return x_1;
}
}
obj* l_Lean_LevelToFormat_Result_max___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_1)) {
case 3:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(3, 1, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
default:
{
obj* x_9; 
x_9 = lean::box(0);
x_2 = x_9;
goto lbl_3;
}
}
lbl_3:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_2);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
obj* l_Lean_LevelToFormat_Result_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_LevelToFormat_Result_max___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_Result_imax___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
default:
{
obj* x_9; 
x_9 = lean::box(0);
x_2 = x_9;
goto lbl_3;
}
}
lbl_3:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_2);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
obj* l_Lean_LevelToFormat_Result_imax(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_LevelToFormat_Result_imax___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_parenIfFalse___main(obj* x_0, uint8 x_1) {
_start:
{
if (x_1 == 0)
{
uint8 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_2 = 0;
x_3 = l_Lean_Format_paren___closed__1;
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = x_4;
x_6 = l_Lean_Format_paren___closed__2;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_2);
x_8 = x_7;
x_9 = l_Lean_Format_paren___closed__3;
x_10 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_Lean_Format_group___main(x_10);
return x_11;
}
else
{
return x_0;
}
}
}
obj* l_Lean_LevelToFormat_parenIfFalse___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_Lean_LevelToFormat_parenIfFalse___main(x_0, x_2);
return x_3;
}
}
obj* l_Lean_LevelToFormat_parenIfFalse(obj* x_0, uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_LevelToFormat_parenIfFalse___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_parenIfFalse___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_Lean_LevelToFormat_parenIfFalse(x_0, x_2);
return x_3;
}
}
obj* l___private_init_lean_level_1__formatLst___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_10 = lean::apply_1(x_0, x_4);
x_11 = 0;
x_12 = lean::box(1);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = x_13;
x_15 = l___private_init_lean_level_1__formatLst___main(x_0, x_6);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_11);
x_17 = x_16;
return x_17;
}
}
}
obj* l___private_init_lean_level_1__formatLst(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_level_1__formatLst___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_fmt___at_Lean_LevelToFormat_Result_format___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Nat_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = 0;
x_8 = l_Lean_LevelToFormat_Result_format___main(x_2, x_7);
x_9 = lean::box(1);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
x_11 = x_10;
x_12 = l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(x_4);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_7);
x_14 = x_13;
return x_14;
}
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("+");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("imax");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_LevelToFormat_Result_format___main(obj* x_0, uint8 x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
return x_2;
}
case 1:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Nat_repr(x_5);
x_9 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
case 2:
{
obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::mk_nat_obj(0ul);
x_16 = lean::nat_dec_eq(x_12, x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_sub(x_12, x_17);
lean::dec(x_12);
x_20 = 0;
x_21 = l_Lean_LevelToFormat_Result_format___main(x_10, x_20);
x_22 = l_Lean_LevelToFormat_Result_format___main___closed__1;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_20);
x_24 = x_23;
x_25 = lean::nat_add(x_18, x_17);
lean::dec(x_18);
x_27 = l_Lean_fmt___at_Lean_LevelToFormat_Result_format___main___spec__1(x_25);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_20);
x_29 = x_28;
x_30 = l_Lean_LevelToFormat_parenIfFalse___main(x_29, x_1);
return x_30;
}
else
{
lean::dec(x_12);
x_0 = x_10;
goto _start;
}
}
case 3:
{
obj* x_33; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
lean::dec(x_0);
x_36 = l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(x_33);
x_37 = 0;
x_38 = l_Lean_LevelToFormat_Result_format___main___closed__2;
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_37);
x_40 = x_39;
x_41 = l_Lean_Format_group___main(x_40);
x_42 = l_Lean_LevelToFormat_parenIfFalse___main(x_41, x_1);
return x_42;
}
default:
{
obj* x_43; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
lean::dec(x_0);
x_46 = l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(x_43);
x_47 = 0;
x_48 = l_Lean_LevelToFormat_Result_format___main___closed__3;
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_46);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_47);
x_50 = x_49;
x_51 = l_Lean_Format_group___main(x_50);
x_52 = l_Lean_LevelToFormat_parenIfFalse___main(x_51, x_1);
return x_52;
}
}
}
}
obj* l_Lean_LevelToFormat_Result_format___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_Lean_LevelToFormat_Result_format___main(x_0, x_2);
return x_3;
}
}
obj* l_Lean_LevelToFormat_Result_format(obj* x_0, uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_LevelToFormat_Result_format___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_Result_format___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_Lean_LevelToFormat_Result_format(x_0, x_2);
return x_3;
}
}
obj* l_Lean_fmt___at_Lean_LevelToFormat_Level_toResult___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Name_toString___closed__1;
x_2 = l_Lean_Name_toStringWithSep___main(x_1, x_0);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Lean_LevelToFormat_Level_toResult___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_LevelToFormat_Level_toResult___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = l_Lean_LevelToFormat_Level_toResult___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_LevelToFormat_Level_toResult___main(x_2);
x_6 = l_Lean_LevelToFormat_Result_succ___main(x_5);
return x_6;
}
case 2:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_LevelToFormat_Level_toResult___main(x_7);
x_13 = l_Lean_LevelToFormat_Level_toResult___main(x_9);
x_14 = l_Lean_LevelToFormat_Result_max___main(x_12, x_13);
return x_14;
}
case 3:
{
obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
lean::dec(x_0);
x_20 = l_Lean_LevelToFormat_Level_toResult___main(x_15);
x_21 = l_Lean_LevelToFormat_Level_toResult___main(x_17);
x_22 = l_Lean_LevelToFormat_Result_imax___main(x_20, x_21);
return x_22;
}
default:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = l_Lean_fmt___at_Lean_LevelToFormat_Level_toResult___main___spec__1(x_23);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
}
}
obj* l_Lean_LevelToFormat_Level_toResult(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_LevelToFormat_Level_toResult___main(x_0);
return x_1;
}
}
obj* l_Lean_LevelToFormat_Level_format(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; 
x_1 = l_Lean_LevelToFormat_Level_toResult___main(x_0);
x_2 = 1;
x_3 = l_Lean_LevelToFormat_Result_format___main(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_LevelToFormat_levelHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_LevelToFormat_Level_format), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_LevelToFormat_levelHasToString() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_HasRepr___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_LevelToFormat_Level_format), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_format(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_level(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
 l_Lean_levelIsInhabited = _init_l_Lean_levelIsInhabited();
lean::mark_persistent(l_Lean_levelIsInhabited);
 l_Lean_Level_one = _init_l_Lean_Level_one();
lean::mark_persistent(l_Lean_Level_one);
 l_Lean_Level_toNat___main___closed__1 = _init_l_Lean_Level_toNat___main___closed__1();
lean::mark_persistent(l_Lean_Level_toNat___main___closed__1);
 l_Lean_LevelToFormat_Result_format___main___closed__1 = _init_l_Lean_LevelToFormat_Result_format___main___closed__1();
lean::mark_persistent(l_Lean_LevelToFormat_Result_format___main___closed__1);
 l_Lean_LevelToFormat_Result_format___main___closed__2 = _init_l_Lean_LevelToFormat_Result_format___main___closed__2();
lean::mark_persistent(l_Lean_LevelToFormat_Result_format___main___closed__2);
 l_Lean_LevelToFormat_Result_format___main___closed__3 = _init_l_Lean_LevelToFormat_Result_format___main___closed__3();
lean::mark_persistent(l_Lean_LevelToFormat_Result_format___main___closed__3);
 l_Lean_LevelToFormat_Level_toResult___main___closed__1 = _init_l_Lean_LevelToFormat_Level_toResult___main___closed__1();
lean::mark_persistent(l_Lean_LevelToFormat_Level_toResult___main___closed__1);
 l_Lean_LevelToFormat_levelHasFormat = _init_l_Lean_LevelToFormat_levelHasFormat();
lean::mark_persistent(l_Lean_LevelToFormat_levelHasFormat);
 l_Lean_LevelToFormat_levelHasToString = _init_l_Lean_LevelToFormat_levelHasToString();
lean::mark_persistent(l_Lean_LevelToFormat_levelHasToString);
return w;
}
