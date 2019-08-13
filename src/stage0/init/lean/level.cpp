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
obj* l_Lean_Level_toOffset___main(obj*);
obj* l_Lean_Level_hasParam___main___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_Level_instantiate(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__4;
obj* l_Lean_LevelToFormat_parenIfFalse(obj*, uint8);
obj* l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__3;
obj* l_Lean_LevelToFormat_Result_max(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__2;
obj* l_Lean_LevelToFormat_Level_toResult(obj*);
extern "C" obj* level_mk_mvar(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_format___main(obj*, uint8);
obj* l___private_init_lean_level_1__formatLst(obj*, obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__5;
obj* l_Lean_Level_mvar___boxed(obj*);
obj* l_Lean_LevelToFormat_levelHasToString___closed__1;
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__1;
obj* l_Lean_Level_ofNat(obj*);
obj* l_Lean_Level_toNat___main(obj*);
obj* l_Lean_Level_Param___boxed(obj*);
obj* l_Lean_Level_instantiate___main(obj*, obj*);
obj* l_Nat_repr(obj*);
extern "C" obj* level_mk_param(obj*);
obj* l_Lean_Level_one;
obj* l_Lean_Level_hasParam___boxed(obj*);
obj* l_Lean_LevelToFormat_Level_format(obj*);
obj* l_Lean_LevelToFormat_parenIfFalse___boxed(obj*, obj*);
obj* l_Lean_LevelToFormat_levelHasFormat___closed__1;
obj* l_Lean_LevelToFormat_Result_succ(obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l___private_init_lean_level_1__formatLst___main(obj*, obj*);
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
obj* l_Lean_Level_max___boxed(obj*, obj*);
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_Lean_Level_imax___boxed(obj*, obj*);
obj* l_Lean_Level_addOffsetAux(obj*, obj*);
obj* l_Lean_Level_ofNat___main___boxed(obj*);
obj* l_Lean_Level_one___closed__1;
obj* l_Lean_Level_toNat___main___boxed(obj*);
extern "C" usize lean_level_hash(obj*);
obj* l_Lean_Nat_imax___boxed(obj*, obj*);
obj* l_Lean_LevelToFormat_Level_toResult___main(obj*);
extern "C" obj* level_mk_succ(obj*);
extern obj* l_System_FilePath_dirName___closed__1;
extern obj* l_Lean_HasRepr___closed__1;
namespace lean {
obj* format_group_core(obj*);
}
obj* l_Lean_LevelToFormat_Result_format___boxed(obj*, obj*);
obj* l_Lean_Level_toNat___main___closed__1;
obj* l_Lean_LevelToFormat_Result_imax(obj*, obj*);
obj* l_Lean_Level_addOffsetAux___main(obj*, obj*);
obj* l_Lean_Level_addOffset(obj*, obj*);
obj* l_Lean_Level_succ___boxed(obj*);
obj* l_Lean_LevelToFormat_levelHasFormat;
obj* l_Lean_LevelToFormat_Result_format(obj*, uint8);
obj* l_Lean_Level_hasMvar___boxed(obj*);
obj* l_Lean_LevelToFormat_Result_format___main___closed__6;
obj* l_Nat_max(obj*, obj*);
obj* l_Lean_Level_hash___boxed(obj*);
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_Lean_levelIsInhabited;
uint8 l_Lean_Level_hasMvar(obj*);
obj* l_Lean_Level_succ___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = level_mk_succ(x_1);
return x_2;
}
}
obj* l_Lean_Level_max___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = level_mk_max(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Level_imax___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = level_mk_imax(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Level_Param___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = level_mk_param(x_1);
return x_2;
}
}
obj* l_Lean_Level_mvar___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = level_mk_mvar(x_1);
return x_2;
}
}
obj* _init_l_Lean_levelIsInhabited() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Lean_Level_one___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = level_mk_succ(x_1);
return x_2;
}
}
obj* _init_l_Lean_Level_one() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Level_one___closed__1;
return x_1;
}
}
uint8 l_Lean_Level_hasParam___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
x_1 = x_2;
goto _start;
}
case 2:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_Level_hasParam___main(x_4);
if (x_6 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
case 3:
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = l_Lean_Level_hasParam___main(x_9);
if (x_11 == 0)
{
x_1 = x_10;
goto _start;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
case 4:
{
uint8 x_14; 
x_14 = 1;
return x_14;
}
default: 
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
}
}
}
obj* l_Lean_Level_hasParam___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Level_hasParam___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Level_hasParam(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Level_hasParam___main(x_1);
return x_2;
}
}
obj* l_Lean_Level_hasParam___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Level_hasParam(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Level_hasMvar(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; uint8 x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = l_Lean_Level_hasParam___main(x_2);
return x_3;
}
case 2:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_Level_hasParam___main(x_4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = l_Lean_Level_hasParam___main(x_5);
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
case 3:
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = l_Lean_Level_hasParam___main(x_9);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = l_Lean_Level_hasParam___main(x_10);
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
case 5:
{
uint8 x_14; 
x_14 = 1;
return x_14;
}
default: 
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
}
}
}
obj* l_Lean_Level_hasMvar___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Level_hasMvar(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_Level_ofNat___main(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
x_6 = l_Lean_Level_ofNat___main(x_5);
lean::dec(x_5);
x_7 = level_mk_succ(x_6);
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
obj* l_Lean_Level_ofNat___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_ofNat___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Level_ofNat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_ofNat___main(x_1);
return x_2;
}
}
obj* l_Lean_Level_ofNat___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_ofNat(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Level_addOffsetAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
x_7 = level_mk_succ(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Lean_Level_addOffsetAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Level_addOffsetAux___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Level_addOffset(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Level_addOffsetAux___main(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Nat_imax(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_Nat_max(x_1, x_2);
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
}
}
obj* l_Lean_Nat_imax___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Nat_imax(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Level_toNat___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Level_toNat___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_Level_toNat___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = l_Lean_Level_toNat___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_4, 0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_7, x_8);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_10, x_11);
lean::dec(x_10);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
case 2:
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
x_16 = l_Lean_Level_toNat___main(x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; 
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_19 = l_Lean_Level_toNat___main(x_15);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; 
lean::dec(x_18);
x_20 = lean::box(0);
return x_20;
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_19, 0);
x_23 = l_Nat_max(x_18, x_22);
lean::dec(x_22);
lean::dec(x_18);
lean::cnstr_set(x_19, 0, x_23);
return x_19;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_19, 0);
lean::inc(x_24);
lean::dec(x_19);
x_25 = l_Nat_max(x_18, x_24);
lean::dec(x_24);
lean::dec(x_18);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
}
}
}
case 3:
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_1, 0);
x_28 = lean::cnstr_get(x_1, 1);
x_29 = l_Lean_Level_toNat___main(x_27);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; 
x_30 = lean::box(0);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
lean::dec(x_29);
x_32 = l_Lean_Level_toNat___main(x_28);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = lean::box(0);
return x_33;
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_32);
if (x_34 == 0)
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_32, 0);
x_36 = l_Lean_Nat_imax(x_31, x_35);
lean::dec(x_35);
lean::dec(x_31);
lean::cnstr_set(x_32, 0, x_36);
return x_32;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_32, 0);
lean::inc(x_37);
lean::dec(x_32);
x_38 = l_Lean_Nat_imax(x_31, x_37);
lean::dec(x_37);
lean::dec(x_31);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
}
}
default: 
{
obj* x_40; 
x_40 = lean::box(0);
return x_40;
}
}
}
}
obj* l_Lean_Level_toNat___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_toNat___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Level_toNat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_toNat___main(x_1);
return x_2;
}
}
obj* l_Lean_Level_toNat___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_toNat(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Level_toOffset___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = l_Lean_Level_toOffset___main(x_2);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_5);
lean::cnstr_set(x_3, 1, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(0u);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_Lean_Level_toOffset(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Level_toOffset___main(x_1);
return x_2;
}
}
obj* l_Lean_Level_instantiate___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_4 = l_Lean_Level_instantiate___main(x_1, x_3);
x_5 = level_mk_succ(x_4);
return x_5;
}
case 2:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_1);
x_8 = l_Lean_Level_instantiate___main(x_1, x_6);
x_9 = l_Lean_Level_instantiate___main(x_1, x_7);
x_10 = level_mk_max(x_8, x_9);
return x_10;
}
case 3:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
lean::inc(x_1);
x_13 = l_Lean_Level_instantiate___main(x_1, x_11);
x_14 = l_Lean_Level_instantiate___main(x_1, x_12);
x_15 = level_mk_imax(x_13, x_14);
return x_15;
}
case 4:
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_1, x_16);
if (lean::obj_tag(x_17) == 0)
{
return x_2;
}
else
{
obj* x_18; 
lean::dec(x_2);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
lean::dec(x_17);
return x_18;
}
}
default: 
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Lean_Level_instantiate(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Level_instantiate___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Level_hash___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean_level_hash(x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
obj* l_Lean_LevelToFormat_Result_succ(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_3);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_6, x_7);
lean::dec(x_6);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
case 2:
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_1);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_11, x_12);
lean::dec(x_11);
lean::cnstr_set(x_1, 1, x_13);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_15, x_16);
lean::dec(x_15);
x_18 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
default: 
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_Lean_LevelToFormat_Result_max(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_2) == 3)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_2, 0, x_11);
return x_2;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
obj* x_15; 
x_15 = lean::box(0);
x_3 = x_15;
goto block_8;
}
block_8:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
}
obj* l_Lean_LevelToFormat_Result_imax(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_2) == 4)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_2, 0, x_11);
return x_2;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
obj* x_15; 
x_15 = lean::box(0);
x_3 = x_15;
goto block_8;
}
block_8:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
}
obj* l_Lean_LevelToFormat_parenIfFalse(obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = 0;
x_4 = l_Lean_Format_paren___closed__2;
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
x_6 = l_Lean_Format_paren___closed__3;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_3);
x_8 = l_Lean_Format_paren___closed__1;
x_9 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::format_group_core(x_9);
return x_10;
}
else
{
return x_1;
}
}
}
obj* l_Lean_LevelToFormat_parenIfFalse___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
lean::dec(x_2);
x_4 = l_Lean_LevelToFormat_parenIfFalse(x_1, x_3);
return x_4;
}
}
obj* l___private_init_lean_level_1__formatLst___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
x_6 = lean::apply_1(x_1, x_4);
x_7 = 0;
x_8 = lean::box(1);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = l___private_init_lean_level_1__formatLst___main(x_1, x_5);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_7);
return x_11;
}
}
}
obj* l___private_init_lean_level_1__formatLst(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_level_1__formatLst___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_fmt___at_Lean_LevelToFormat_Result_format___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = 0;
x_6 = l_Lean_LevelToFormat_Result_format___main(x_3, x_5);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_5);
x_9 = l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(x_4);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_5);
return x_10;
}
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("+");
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_LevelToFormat_Result_format___main___closed__1;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("max");
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_LevelToFormat_Result_format___main___closed__3;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("imax");
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_Result_format___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_LevelToFormat_Result_format___main___closed__5;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_Result_format___main(obj* x_1, uint8 x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
return x_3;
}
case 1:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Nat_repr(x_4);
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
case 2:
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_8, x_11);
lean::dec(x_8);
x_13 = 0;
x_14 = l_Lean_LevelToFormat_Result_format___main(x_7, x_13);
x_15 = l_Lean_LevelToFormat_Result_format___main___closed__2;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_13);
x_17 = lean::nat_add(x_12, x_11);
lean::dec(x_12);
x_18 = l_Lean_fmt___at_Lean_LevelToFormat_Result_format___main___spec__1(x_17);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_13);
x_20 = l_Lean_LevelToFormat_parenIfFalse(x_19, x_2);
return x_20;
}
else
{
lean::dec(x_8);
x_1 = x_7;
goto _start;
}
}
case 3:
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
lean::dec(x_1);
x_23 = l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(x_22);
x_24 = 0;
x_25 = l_Lean_LevelToFormat_Result_format___main___closed__4;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_24);
x_27 = lean::format_group_core(x_26);
x_28 = l_Lean_LevelToFormat_parenIfFalse(x_27, x_2);
return x_28;
}
default: 
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
lean::dec(x_1);
x_30 = l___private_init_lean_level_1__formatLst___main___at_Lean_LevelToFormat_Result_format___main___spec__2(x_29);
x_31 = 0;
x_32 = l_Lean_LevelToFormat_Result_format___main___closed__6;
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_30);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_31);
x_34 = lean::format_group_core(x_33);
x_35 = l_Lean_LevelToFormat_parenIfFalse(x_34, x_2);
return x_35;
}
}
}
}
obj* l_Lean_LevelToFormat_Result_format___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
lean::dec(x_2);
x_4 = l_Lean_LevelToFormat_Result_format___main(x_1, x_3);
return x_4;
}
}
obj* l_Lean_LevelToFormat_Result_format(obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_LevelToFormat_Result_format___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_LevelToFormat_Result_format___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
lean::dec(x_2);
x_4 = l_Lean_LevelToFormat_Result_format(x_1, x_3);
return x_4;
}
}
obj* l_Lean_fmt___at_Lean_LevelToFormat_Level_toResult___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_Lean_LevelToFormat_Level_toResult___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_Level_toResult___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_LevelToFormat_Level_toResult___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_LevelToFormat_Level_toResult___main(x_3);
x_5 = l_Lean_LevelToFormat_Result_succ(x_4);
return x_5;
}
case 2:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = l_Lean_LevelToFormat_Level_toResult___main(x_6);
x_9 = l_Lean_LevelToFormat_Level_toResult___main(x_7);
x_10 = l_Lean_LevelToFormat_Result_max(x_8, x_9);
return x_10;
}
case 3:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_13 = l_Lean_LevelToFormat_Level_toResult___main(x_11);
x_14 = l_Lean_LevelToFormat_Level_toResult___main(x_12);
x_15 = l_Lean_LevelToFormat_Result_imax(x_13, x_14);
return x_15;
}
default: 
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_17 = l_Lean_fmt___at_Lean_LevelToFormat_Level_toResult___main___spec__1(x_16);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
obj* l_Lean_LevelToFormat_Level_toResult(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_LevelToFormat_Level_toResult___main(x_1);
return x_2;
}
}
obj* l_Lean_LevelToFormat_Level_format(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; 
x_2 = l_Lean_LevelToFormat_Level_toResult___main(x_1);
x_3 = 1;
x_4 = l_Lean_LevelToFormat_Result_format___main(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_LevelToFormat_levelHasFormat___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_LevelToFormat_Level_format), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_levelHasFormat() {
_start:
{
obj* x_1; 
x_1 = l_Lean_LevelToFormat_levelHasFormat___closed__1;
return x_1;
}
}
obj* _init_l_Lean_LevelToFormat_levelHasToString___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_LevelToFormat_levelHasFormat___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_LevelToFormat_levelHasToString() {
_start:
{
obj* x_1; 
x_1 = l_Lean_LevelToFormat_levelHasToString___closed__1;
return x_1;
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
l_Lean_Level_one___closed__1 = _init_l_Lean_Level_one___closed__1();
lean::mark_persistent(l_Lean_Level_one___closed__1);
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
l_Lean_LevelToFormat_Result_format___main___closed__4 = _init_l_Lean_LevelToFormat_Result_format___main___closed__4();
lean::mark_persistent(l_Lean_LevelToFormat_Result_format___main___closed__4);
l_Lean_LevelToFormat_Result_format___main___closed__5 = _init_l_Lean_LevelToFormat_Result_format___main___closed__5();
lean::mark_persistent(l_Lean_LevelToFormat_Result_format___main___closed__5);
l_Lean_LevelToFormat_Result_format___main___closed__6 = _init_l_Lean_LevelToFormat_Result_format___main___closed__6();
lean::mark_persistent(l_Lean_LevelToFormat_Result_format___main___closed__6);
l_Lean_LevelToFormat_Level_toResult___main___closed__1 = _init_l_Lean_LevelToFormat_Level_toResult___main___closed__1();
lean::mark_persistent(l_Lean_LevelToFormat_Level_toResult___main___closed__1);
l_Lean_LevelToFormat_levelHasFormat___closed__1 = _init_l_Lean_LevelToFormat_levelHasFormat___closed__1();
lean::mark_persistent(l_Lean_LevelToFormat_levelHasFormat___closed__1);
l_Lean_LevelToFormat_levelHasFormat = _init_l_Lean_LevelToFormat_levelHasFormat();
lean::mark_persistent(l_Lean_LevelToFormat_levelHasFormat);
l_Lean_LevelToFormat_levelHasToString___closed__1 = _init_l_Lean_LevelToFormat_levelHasToString___closed__1();
lean::mark_persistent(l_Lean_LevelToFormat_levelHasToString___closed__1);
l_Lean_LevelToFormat_levelHasToString = _init_l_Lean_LevelToFormat_levelHasToString();
lean::mark_persistent(l_Lean_LevelToFormat_levelHasToString);
return w;
}
