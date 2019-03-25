// Lean compiler output
// Module: init.lean.compiler.constfolding
// Imports: init.lean.expr init.platform init.lean.compiler.util
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
obj* l_Lean_Compiler_natFoldFns;
obj* l_Lean_Compiler_toDecidableExpr___closed__1;
obj* l_Nat_decLe___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_mkBinApp(obj*, obj*, obj*);
obj* l_Lean_Compiler_foldNatDecLt___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Compiler_foldNatDiv(uint8);
obj* l_Lean_Compiler_foldUIntMod___lambda__1___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Compiler_isOfNat(obj*);
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main(obj*);
obj* l_Lean_Compiler_foldUIntMod(uint8, obj*, obj*);
obj* l_Lean_Compiler_foldNatMul___boxed(obj*);
obj* l_Lean_Compiler_foldNatDiv___boxed(obj*);
obj* l_Lean_Compiler_getInfoFromFn___main(obj*, obj*);
obj* l_Nat_div___boxed(obj*, obj*);
obj* l_Lean_Compiler_getNumLit___main(obj*);
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(obj*, obj*);
obj* l_Lean_Compiler_getInfoFromFn___main___boxed(obj*, obj*);
obj* l_Lean_Compiler_getInfoFromVal(obj*);
obj* l_Lean_Compiler_foldUIntSub___lambda__1(obj*, uint8, obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Compiler_foldNatDecLe___closed__2;
obj* l_Lean_Compiler_foldBinUInt(obj*, uint8, obj*, obj*);
obj* l_Lean_Compiler_getInfoFromVal___main(obj*);
obj* l_Lean_Compiler_foldNatMod___boxed(obj*);
obj* l_Lean_Compiler_getInfoFromFn(obj*, obj*);
obj* l_Lean_Compiler_mkNatLt(obj*, obj*);
obj* l___private_init_lean_compiler_constfolding_1__alistFind___boxed(obj*);
obj* l_Lean_Compiler_foldNatMod___rarg(obj*, obj*);
obj* l_Lean_Compiler_foldNatSucc(uint8);
extern obj* l_Lean_mkDecIsFalse___closed__1;
extern obj* l_System_platform_nbits;
obj* l_Lean_Compiler_foldUIntAdd___boxed(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Compiler_uintBinFoldFns___spec__2(obj*, obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Lean_Compiler_unFoldFns;
obj* l_Lean_Compiler_foldNatDecEq___closed__2;
obj* l_Lean_Compiler_foldUIntMod___lambda__1(obj*, uint8, obj*, obj*);
obj* l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1___boxed(obj*, obj*);
obj* l_Lean_Compiler_findUnFoldFn___boxed(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Compiler_mkNatEq___closed__1;
obj* l_Lean_Compiler_findBinFoldFn___boxed(obj*);
obj* l_Lean_Compiler_foldUIntDiv___lambda__1(obj*, uint8, obj*, obj*);
obj* l_Lean_Compiler_foldBinOp___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
extern obj* l_Lean_Level_one;
obj* l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_foldNatDecEq___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_isOfNat___boxed(obj*);
obj* l_Lean_Compiler_foldCharOfNat___closed__1;
obj* l_Lean_Compiler_findUnFoldFn(obj*);
obj* l_Lean_Compiler_foldNatAdd___rarg(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Compiler_foldCharOfNat(uint8, obj*);
obj* l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1(obj*, obj*);
obj* l_Lean_Compiler_foldNatBinPred(obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_Compiler_mkNatLe___closed__1;
obj* l_Lean_Compiler_foldUIntMul(uint8, obj*, obj*);
obj* l_Lean_Compiler_mkNatLt___closed__1;
obj* l_Lean_Compiler_foldNatMod___rarg___closed__1;
obj* l_Lean_Compiler_foldNatAdd(uint8);
obj* l_Nat_mul___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkUInt32Lit___boxed(obj*);
obj* l_Lean_Compiler_foldUIntAdd___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_foldNatMul___rarg___closed__1;
obj* l_Lean_Compiler_foldUIntMul___lambda__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_mkDecIsTrue___closed__1;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_Lean_Compiler_mkUIntLit___boxed(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Compiler_uintBinFoldFns___spec__2___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkUIntTypeName(obj*);
obj* l_Lean_Compiler_foldNatDiv___rarg___closed__1;
obj* l_Lean_Compiler_foldNatSucc___boxed(obj*);
obj* l_Lean_Compiler_foldUIntMod___closed__1;
uint8 l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1(obj*, uint8, obj*);
obj* l_Lean_Compiler_mkUInt32Lit(obj*);
obj* l_Lean_Compiler_foldNatDecLe(uint8, obj*, obj*);
obj* l_Lean_Compiler_mkUInt32Lit___closed__1;
obj* l_List_append___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Compiler_foldUnOp___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Compiler_foldUIntMul___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_foldUIntDiv___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_foldNatDecLe___closed__1;
obj* l_Nat_add___boxed(obj*, obj*);
obj* l_Lean_Compiler_toDecidableExpr(uint8, obj*, uint8);
obj* l_Lean_Compiler_foldNatDecLe___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_foldUIntMul___closed__1;
obj* l_Lean_Compiler_foldNatDecEq___closed__1;
obj* l_Lean_Compiler_foldCharOfNat___boxed(obj*, obj*);
obj* l_Lean_Compiler_numScalarTypes;
obj* l_Lean_Compiler_foldNatBinPred___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_foldNatDecLt___closed__2;
obj* l_Lean_Compiler_findBinFoldFn(obj*);
obj* l_Lean_Compiler_foldUIntAdd(uint8, obj*, obj*);
obj* l_Lean_Compiler_foldNatSucc___rarg(obj*);
obj* l_Lean_Compiler_getInfoFromFn___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkUIntLit(obj*, obj*);
namespace lean {
obj* fold_bin_op_core(uint8, obj*, obj*, obj*);
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___rarg(obj*, obj*);
obj* l_Nat_pow___main(obj*, obj*);
obj* l_Lean_Compiler_toDecidableExpr___closed__2;
obj* l_Lean_Compiler_foldNatDiv___rarg(obj*, obj*);
obj* l_Lean_Compiler_foldBinUInt___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_foldUIntSub___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_decLt___boxed(obj*, obj*);
namespace lean {
obj* fold_un_op_core(uint8, obj*, obj*);
}
obj* l_Lean_Compiler_foldUIntAdd___closed__1;
obj* l_Lean_Compiler_foldUIntSub___closed__1;
obj* l_Lean_Compiler_foldNatDecEq(uint8, obj*, obj*);
obj* l_Lean_Compiler_foldUIntDiv___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_mkUIntTypeName___closed__1;
obj* l_Lean_Compiler_uintBinFoldFns;
obj* l_Lean_Compiler_foldNatMul___rarg(obj*, obj*);
obj* l_Lean_Compiler_foldUIntSub___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_constfolding_1__alistFind___rarg___boxed(obj*, obj*);
extern obj* l_Lean_Compiler_mkLcProof___closed__1;
obj* l_Lean_Compiler_foldUIntAdd___lambda__1(obj*, uint8, obj*, obj*);
obj* l_Lean_Compiler_foldUIntMul___lambda__1(obj*, uint8, obj*, obj*);
obj* l_Lean_Compiler_foldUIntDiv(uint8, obj*, obj*);
obj* l_Lean_Compiler_binFoldFns;
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_Compiler_foldUIntDiv___closed__1;
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main___boxed(obj*);
obj* l_Lean_Compiler_foldNatDecLt(uint8, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Lean_Compiler_foldNatAdd___rarg___closed__1;
obj* l_Lean_Compiler_getInfoFromVal___boxed(obj*);
obj* l_Lean_Compiler_getInfoFromVal___main___boxed(obj*);
obj* l___private_init_lean_compiler_constfolding_1__alistFind(obj*);
namespace lean {
obj* get_num_lit_core(obj*);
}
obj* l_Lean_Compiler_toDecidableExpr___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Compiler_neutralExpr;
obj* l_Lean_Compiler_foldNatMod(uint8);
obj* l_Lean_Compiler_foldNatAdd___boxed(obj*);
obj* l_Lean_Compiler_foldNatMul(uint8);
obj* l_Lean_Name_append___main(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Nat_mod___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg___boxed(obj*, obj*);
obj* l_Lean_Compiler_foldUIntSub(uint8, obj*, obj*);
obj* l_Lean_Compiler_foldNatBinOp(obj*, obj*, obj*);
obj* l_Lean_Compiler_foldUIntMod___boxed(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_Lean_Compiler_mkNatEq(obj*, obj*);
obj* l_Lean_Compiler_preUIntBinFoldFns;
obj* l_Lean_Compiler_foldNatDecLt___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkNatLe(obj*, obj*);
obj* _init_l_Lean_Compiler_mkUIntTypeName___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("UInt");
return x_0;
}
}
obj* l_Lean_Compiler_mkUIntTypeName(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = l_Nat_repr(x_0);
x_2 = l_Lean_Compiler_mkUIntTypeName___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean_name_mk_string(x_5, x_3);
return x_6;
}
}
obj* _init_l_Lean_Compiler_numScalarTypes() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_0 = lean::mk_nat_obj(8u);
x_1 = l_Lean_Compiler_mkUIntTypeName(x_0);
x_2 = lean::mk_string("ofNat");
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean_name_mk_string(x_1, x_2);
x_6 = lean::mk_nat_obj(2u);
x_7 = l_Nat_pow___main(x_6, x_0);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_1);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_7);
x_9 = lean::mk_nat_obj(16u);
x_10 = l_Lean_Compiler_mkUIntTypeName(x_9);
lean::inc(x_2);
lean::inc(x_10);
x_13 = lean_name_mk_string(x_10, x_2);
x_14 = l_Nat_pow___main(x_6, x_9);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_9);
lean::cnstr_set(x_15, 1, x_10);
lean::cnstr_set(x_15, 2, x_13);
lean::cnstr_set(x_15, 3, x_14);
x_16 = lean::mk_nat_obj(32u);
x_17 = l_Lean_Compiler_mkUIntTypeName(x_16);
lean::inc(x_2);
lean::inc(x_17);
x_20 = lean_name_mk_string(x_17, x_2);
x_21 = l_Nat_pow___main(x_6, x_16);
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_20);
lean::cnstr_set(x_22, 3, x_21);
x_23 = lean::mk_nat_obj(64u);
x_24 = l_Lean_Compiler_mkUIntTypeName(x_23);
lean::inc(x_2);
lean::inc(x_24);
x_27 = lean_name_mk_string(x_24, x_2);
x_28 = l_Nat_pow___main(x_6, x_23);
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_23);
lean::cnstr_set(x_29, 1, x_24);
lean::cnstr_set(x_29, 2, x_27);
lean::cnstr_set(x_29, 3, x_28);
x_30 = lean::box(0);
x_31 = lean::mk_string("Usize");
x_32 = lean_name_mk_string(x_30, x_31);
lean::inc(x_32);
x_34 = lean_name_mk_string(x_32, x_2);
x_35 = l_System_platform_nbits;
x_36 = l_Nat_pow___main(x_6, x_35);
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_32);
lean::cnstr_set(x_37, 2, x_34);
lean::cnstr_set(x_37, 3, x_36);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_29);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_22);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_15);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_8);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
uint8 l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = lean_name_dec_eq(x_5, x_0);
if (x_6 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8 l_Lean_Compiler_isOfNat(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; uint8 x_3; 
x_1 = 0;
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
x_4 = l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1(x_0, x_3, x_2);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Compiler_isOfNat___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Compiler_isOfNat(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Compiler_getInfoFromFn___main(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_8; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
x_10 = lean_name_dec_eq(x_8, x_0);
lean::dec(x_8);
if (x_10 == 0)
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_5);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_3);
return x_15;
}
}
}
}
obj* l_Lean_Compiler_getInfoFromFn___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_getInfoFromFn___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Compiler_getInfoFromFn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_getInfoFromFn___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Compiler_getInfoFromFn___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_getInfoFromFn(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Compiler_getInfoFromVal___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 5:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_Lean_Compiler_getInfoFromFn___main(x_2, x_3);
return x_4;
}
default:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
}
default:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
}
}
obj* l_Lean_Compiler_getInfoFromVal___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_getInfoFromVal___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_getInfoFromVal(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_getInfoFromVal___main(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_getInfoFromVal___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_getInfoFromVal(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_getNumLit___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 5:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_3; obj* x_6; uint8 x_9; obj* x_10; uint8 x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = 0;
x_10 = l_Lean_Compiler_numScalarTypes;
x_11 = l_List_foldr___main___at_Lean_Compiler_isOfNat___spec__1(x_6, x_9, x_10);
lean::dec(x_6);
if (x_11 == 0)
{
obj* x_14; 
lean::dec(x_3);
x_14 = lean::box(0);
return x_14;
}
else
{
x_0 = x_3;
goto _start;
}
}
default:
{
obj* x_18; 
lean::dec(x_1);
lean::dec(x_0);
x_18 = lean::box(0);
return x_18;
}
}
}
case 9:
{
obj* x_19; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
return x_25;
}
else
{
obj* x_27; 
lean::dec(x_19);
x_27 = lean::box(0);
return x_27;
}
}
default:
{
obj* x_29; 
lean::dec(x_0);
x_29 = lean::box(0);
return x_29;
}
}
}
}
namespace lean {
obj* get_num_lit_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_getNumLit___main(x_0);
return x_1;
}
}
}
obj* l_Lean_Compiler_mkUIntLit(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_2, x_4);
x_6 = lean::cnstr_get(x_0, 3);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::nat_mod(x_1, x_6);
lean::dec(x_6);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_9);
x_12 = lean_expr_mk_lit(x_11);
x_13 = lean_expr_mk_app(x_5, x_12);
return x_13;
}
}
obj* l_Lean_Compiler_mkUIntLit___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_mkUIntLit(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_mkUInt32Lit___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_nat_obj(32u);
x_1 = l_Lean_Compiler_mkUIntTypeName(x_0);
x_2 = lean::mk_string("ofNat");
lean::inc(x_1);
x_4 = lean_name_mk_string(x_1, x_2);
x_5 = lean::mk_nat_obj(2u);
x_6 = l_Nat_pow___main(x_5, x_0);
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_6);
return x_7;
}
}
obj* l_Lean_Compiler_mkUInt32Lit(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Compiler_mkUInt32Lit___closed__1;
x_2 = l_Lean_Compiler_mkUIntLit(x_1, x_0);
return x_2;
}
}
obj* l_Lean_Compiler_mkUInt32Lit___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_mkUInt32Lit(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_foldBinUInt(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_Lean_Compiler_getNumLit___main(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_Lean_Compiler_getNumLit___main(x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
lean::dec(x_13);
x_21 = l_Lean_Compiler_getInfoFromVal___main(x_2);
lean::dec(x_2);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; 
lean::dec(x_18);
lean::dec(x_10);
lean::dec(x_0);
x_26 = lean::box(0);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_35; 
x_27 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_29 = x_21;
} else {
 lean::inc(x_27);
 lean::dec(x_21);
 x_29 = lean::box(0);
}
x_30 = lean::box(x_1);
lean::inc(x_27);
x_32 = lean::apply_4(x_0, x_27, x_30, x_10, x_18);
x_33 = l_Lean_Compiler_mkUIntLit(x_27, x_32);
lean::dec(x_32);
if (lean::is_scalar(x_29)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_29;
}
lean::cnstr_set(x_35, 0, x_33);
return x_35;
}
}
}
}
}
obj* l_Lean_Compiler_foldBinUInt___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_Compiler_foldBinUInt(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Compiler_foldUIntAdd___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::nat_add(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_foldUIntAdd___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntAdd___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldUIntAdd(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Compiler_foldUIntAdd___closed__1;
x_4 = l_Lean_Compiler_foldBinUInt(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntAdd___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_Compiler_foldUIntAdd___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Compiler_foldUIntAdd___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldUIntAdd(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntMul___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::nat_mul(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_foldUIntMul___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntMul___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldUIntMul(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Compiler_foldUIntMul___closed__1;
x_4 = l_Lean_Compiler_foldBinUInt(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntMul___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_Compiler_foldUIntMul___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Compiler_foldUIntMul___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldUIntMul(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntDiv___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::nat_div(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_foldUIntDiv___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntDiv___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldUIntDiv(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Compiler_foldUIntDiv___closed__1;
x_4 = l_Lean_Compiler_foldBinUInt(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntDiv___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_Compiler_foldUIntDiv___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Compiler_foldUIntDiv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldUIntDiv(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntMod___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::nat_mod(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_foldUIntMod___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntMod___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldUIntMod(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Compiler_foldUIntMod___closed__1;
x_4 = l_Lean_Compiler_foldBinUInt(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntMod___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_Compiler_foldUIntMod___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Compiler_foldUIntMod___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldUIntMod(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntSub___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 3);
x_5 = lean::nat_sub(x_4, x_3);
x_6 = lean::nat_add(x_2, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Compiler_foldUIntSub___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntSub___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldUIntSub(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Compiler_foldUIntSub___closed__1;
x_4 = l_Lean_Compiler_foldBinUInt(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Compiler_foldUIntSub___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_Compiler_foldUIntSub___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Compiler_foldUIntSub___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldUIntSub(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_preUIntBinFoldFns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::box(0);
x_1 = lean::mk_string("add");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntAdd___boxed), 3, 0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("mul");
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntMul___boxed), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::mk_string("div");
x_10 = lean_name_mk_string(x_0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntDiv___boxed), 3, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::mk_string("mod");
x_14 = lean_name_mk_string(x_0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntMod___boxed), 3, 0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_string("sub");
x_18 = lean_name_mk_string(x_0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldUIntSub___boxed), 3, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_12);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_8);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_4);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
obj* l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_12 = x_3;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_3);
 x_12 = lean::box(0);
}
x_13 = l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1(x_0, x_5);
x_14 = lean::cnstr_get(x_0, 1);
x_15 = l_Lean_Name_append___main(x_14, x_8);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_10);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
return x_17;
}
}
}
obj* l_List_foldl___main___at_Lean_Compiler_uintBinFoldFns___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_Compiler_preUIntBinFoldFns;
x_5 = l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1(x_2, x_4);
x_6 = l_List_append___rarg(x_0, x_5);
x_0 = x_6;
x_1 = x_3;
goto _start;
}
}
}
obj* _init_l_Lean_Compiler_uintBinFoldFns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_Lean_Compiler_numScalarTypes;
x_2 = l_List_foldl___main___at_Lean_Compiler_uintBinFoldFns___spec__2(x_0, x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_Lean_Compiler_uintBinFoldFns___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_foldl___main___at_Lean_Compiler_uintBinFoldFns___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_Lean_Compiler_uintBinFoldFns___spec__2(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Compiler_foldNatBinOp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_getNumLit___main(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_10 = l_Lean_Compiler_getNumLit___main(x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
lean::dec(x_7);
lean::dec(x_0);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::apply_2(x_0, x_7, x_14);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean_expr_mk_lit(x_18);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
}
obj* _init_l_Lean_Compiler_foldNatAdd___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_add___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatAdd___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_foldNatAdd___rarg___closed__1;
x_3 = l_Lean_Compiler_foldNatBinOp(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Compiler_foldNatAdd(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatAdd___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Compiler_foldNatAdd___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_Compiler_foldNatAdd(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_foldNatMul___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatMul___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_foldNatMul___rarg___closed__1;
x_3 = l_Lean_Compiler_foldNatBinOp(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Compiler_foldNatMul(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatMul___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Compiler_foldNatMul___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_Compiler_foldNatMul(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_foldNatDiv___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_div___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatDiv___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_foldNatDiv___rarg___closed__1;
x_3 = l_Lean_Compiler_foldNatBinOp(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Compiler_foldNatDiv(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatDiv___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Compiler_foldNatDiv___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_Compiler_foldNatDiv(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_foldNatMod___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mod___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatMod___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_foldNatMod___rarg___closed__1;
x_3 = l_Lean_Compiler_foldNatBinOp(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Compiler_foldNatMod(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatMod___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Compiler_foldNatMod___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_Compiler_foldNatMod(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_mkNatEq___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Eq");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_Lean_Level_one;
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean_expr_mk_const(x_2, x_5);
x_7 = lean::mk_string("Nat");
x_8 = lean_name_mk_string(x_0, x_7);
x_9 = lean_expr_mk_const(x_8, x_3);
x_10 = lean_expr_mk_app(x_6, x_9);
return x_10;
}
}
obj* l_Lean_Compiler_mkNatEq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_mkNatEq___closed__1;
x_3 = l_Lean_mkBinApp(x_2, x_0, x_1);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkNatLt___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = lean::mk_string("HasLt");
lean::inc(x_1);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("lt");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::box(0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean_expr_mk_const(x_5, x_8);
x_10 = lean::mk_string("Nat");
x_11 = lean_name_mk_string(x_0, x_10);
lean::inc(x_11);
x_13 = lean_expr_mk_const(x_11, x_6);
x_14 = lean_name_mk_string(x_11, x_1);
x_15 = lean_expr_mk_const(x_14, x_6);
x_16 = l_Lean_mkBinApp(x_9, x_13, x_15);
return x_16;
}
}
obj* l_Lean_Compiler_mkNatLt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_mkNatLt___closed__1;
x_3 = l_Lean_mkBinApp(x_2, x_0, x_1);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkNatLe___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = lean::mk_string("HasLt");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("le");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::box(0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = lean_expr_mk_const(x_4, x_7);
x_9 = lean::mk_string("Nat");
x_10 = lean_name_mk_string(x_0, x_9);
lean::inc(x_10);
x_12 = lean_expr_mk_const(x_10, x_5);
x_13 = lean::mk_string("HasLe");
x_14 = lean_name_mk_string(x_10, x_13);
x_15 = lean_expr_mk_const(x_14, x_5);
x_16 = l_Lean_mkBinApp(x_8, x_12, x_15);
return x_16;
}
}
obj* l_Lean_Compiler_mkNatLe(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_mkNatLe___closed__1;
x_3 = l_Lean_mkBinApp(x_2, x_0, x_1);
return x_3;
}
}
obj* _init_l_Lean_Compiler_toDecidableExpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_mkDecIsFalse___closed__1;
x_1 = l_Lean_Compiler_neutralExpr;
x_2 = l_Lean_mkBinApp(x_0, x_1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_toDecidableExpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_mkDecIsTrue___closed__1;
x_1 = l_Lean_Compiler_neutralExpr;
x_2 = l_Lean_mkBinApp(x_0, x_1, x_1);
return x_2;
}
}
obj* l_Lean_Compiler_toDecidableExpr(uint8 x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_0 == 0)
{
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; 
x_4 = l_Lean_Compiler_toDecidableExpr___closed__1;
return x_4;
}
else
{
obj* x_5; 
x_5 = l_Lean_Compiler_toDecidableExpr___closed__2;
return x_5;
}
}
else
{
if (x_2 == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = l_Lean_Compiler_mkLcProof___closed__1;
lean::inc(x_1);
x_8 = lean_expr_mk_app(x_6, x_1);
x_9 = l_Lean_mkDecIsFalse___closed__1;
x_10 = l_Lean_mkBinApp(x_9, x_1, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_11 = l_Lean_Compiler_mkLcProof___closed__1;
lean::inc(x_1);
x_13 = lean_expr_mk_app(x_11, x_1);
x_14 = l_Lean_mkDecIsTrue___closed__1;
x_15 = l_Lean_mkBinApp(x_14, x_1, x_13);
return x_15;
}
}
}
}
obj* l_Lean_Compiler_toDecidableExpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_0);
x_4 = lean::unbox(x_2);
x_5 = l_Lean_Compiler_toDecidableExpr(x_3, x_1, x_4);
return x_5;
}
}
obj* l_Lean_Compiler_foldNatBinPred(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::inc(x_3);
x_6 = l_Lean_Compiler_getNumLit___main(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; obj* x_16; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
lean::inc(x_4);
x_16 = l_Lean_Compiler_getNumLit___main(x_4);
if (lean::obj_tag(x_16) == 0)
{
obj* x_22; 
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_22 = lean::box(0);
return x_22;
}
else
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_25 = x_16;
} else {
 lean::inc(x_23);
 lean::dec(x_16);
 x_25 = lean::box(0);
}
x_26 = lean::apply_2(x_0, x_3, x_4);
x_27 = lean::apply_2(x_1, x_12, x_23);
x_28 = lean::unbox(x_27);
x_29 = l_Lean_Compiler_toDecidableExpr(x_2, x_26, x_28);
if (lean::is_scalar(x_25)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_25;
}
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
}
}
obj* l_Lean_Compiler_foldNatBinPred___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_Lean_Compiler_foldNatBinPred(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _init_l_Lean_Compiler_foldNatDecEq___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_mkNatEq), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Compiler_foldNatDecEq___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatDecEq(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Compiler_foldNatDecEq___closed__1;
x_4 = l_Lean_Compiler_foldNatDecEq___closed__2;
x_5 = l_Lean_Compiler_foldNatBinPred(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_Lean_Compiler_foldNatDecEq___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldNatDecEq(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_foldNatDecLt___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_mkNatLt), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Compiler_foldNatDecLt___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decLt___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatDecLt(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Compiler_foldNatDecLt___closed__1;
x_4 = l_Lean_Compiler_foldNatDecLt___closed__2;
x_5 = l_Lean_Compiler_foldNatBinPred(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_Lean_Compiler_foldNatDecLt___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldNatDecLt(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_foldNatDecLe___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_mkNatLe), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Compiler_foldNatDecLe___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decLe___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Compiler_foldNatDecLe(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Compiler_foldNatDecLe___closed__1;
x_4 = l_Lean_Compiler_foldNatDecLe___closed__2;
x_5 = l_Lean_Compiler_foldNatBinPred(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_Lean_Compiler_foldNatDecLe___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_Compiler_foldNatDecLe(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_natFoldFns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Nat");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("add");
lean::inc(x_2);
x_5 = lean_name_mk_string(x_2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatAdd___boxed), 1, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("mul");
lean::inc(x_2);
x_10 = lean_name_mk_string(x_2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatMul___boxed), 1, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::mk_string("div");
lean::inc(x_2);
x_15 = lean_name_mk_string(x_2, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatDiv___boxed), 1, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_string("mod");
lean::inc(x_2);
x_20 = lean_name_mk_string(x_2, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatMod___boxed), 1, 0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::mk_string("decEq");
lean::inc(x_2);
x_25 = lean_name_mk_string(x_2, x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatDecEq___boxed), 3, 0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_string("decLt");
lean::inc(x_2);
x_30 = lean_name_mk_string(x_2, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatDecLt___boxed), 3, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::mk_string("decLe");
x_34 = lean_name_mk_string(x_2, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatDecLe___boxed), 3, 0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_32);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_27);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_22);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_17);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_12);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_7);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
obj* _init_l_Lean_Compiler_binFoldFns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Compiler_uintBinFoldFns;
x_1 = l_Lean_Compiler_natFoldFns;
x_2 = l_List_append___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Compiler_foldNatSucc___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_getNumLit___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_3, x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_7);
x_10 = lean_expr_mk_lit(x_9);
if (lean::is_scalar(x_5)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_5;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_Lean_Compiler_foldNatSucc(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatSucc___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Compiler_foldNatSucc___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_Compiler_foldNatSucc(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_foldCharOfNat___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Lean_Compiler_mkUInt32Lit___closed__1;
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_Compiler_mkUIntLit(x_0, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Compiler_foldCharOfNat(uint8 x_0, obj* x_1) {
_start:
{
if (x_0 == 0)
{
obj* x_2; 
x_2 = l_Lean_Compiler_getNumLit___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; uint32 x_7; uint32 x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::uint32_of_nat(x_4);
x_8 = 55296;
x_9 = x_7 < x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = 57343;
x_11 = x_10 < x_7;
if (x_11 == 0)
{
obj* x_14; 
lean::dec(x_6);
lean::dec(x_4);
x_14 = l_Lean_Compiler_foldCharOfNat___closed__1;
return x_14;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = 1114112;
x_16 = x_7 < x_15;
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_6);
lean::dec(x_4);
x_19 = l_Lean_Compiler_foldCharOfNat___closed__1;
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_23; 
x_20 = l_Lean_Compiler_mkUInt32Lit___closed__1;
x_21 = l_Lean_Compiler_mkUIntLit(x_20, x_4);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_6;
}
lean::cnstr_set(x_23, 0, x_21);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l_Lean_Compiler_mkUInt32Lit___closed__1;
x_25 = l_Lean_Compiler_mkUIntLit(x_24, x_4);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_6;
}
lean::cnstr_set(x_27, 0, x_25);
return x_27;
}
}
}
else
{
obj* x_29; 
lean::dec(x_1);
x_29 = lean::box(0);
return x_29;
}
}
}
obj* l_Lean_Compiler_foldCharOfNat___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_Lean_Compiler_foldCharOfNat(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Compiler_unFoldFns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Nat");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("succ");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldNatSucc___boxed), 1, 0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("Char");
x_8 = lean_name_mk_string(x_0, x_7);
x_9 = lean::mk_string("ofNat");
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_foldCharOfNat___boxed), 2, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_8; obj* x_10; uint8 x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean_name_dec_eq(x_0, x_8);
lean::dec(x_8);
if (x_13 == 0)
{
lean::dec(x_10);
x_1 = x_5;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_5);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_10);
return x_18;
}
}
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_constfolding_1__alistFind___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_constfolding_1__alistFind___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_constfolding_1__alistFind___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_constfolding_1__alistFind___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_constfolding_1__alistFind(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_findBinFoldFn(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Compiler_binFoldFns;
x_2 = l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Compiler_findBinFoldFn___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_findBinFoldFn(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_findUnFoldFn(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Compiler_unFoldFns;
x_2 = l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Compiler_findUnFoldFn___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_findUnFoldFn(x_0);
lean::dec(x_0);
return x_1;
}
}
namespace lean {
obj* fold_bin_op_core(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_Lean_Compiler_binFoldFns;
x_8 = l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(x_4, x_7);
lean::dec(x_4);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_3);
lean::dec(x_2);
x_12 = lean::box(0);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::box(x_0);
x_17 = lean::apply_3(x_13, x_16, x_2, x_3);
return x_17;
}
}
default:
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_21 = lean::box(0);
return x_21;
}
}
}
}
}
obj* l_Lean_Compiler_foldBinOp___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = lean::fold_bin_op_core(x_4, x_1, x_2, x_3);
return x_5;
}
}
namespace lean {
obj* fold_un_op_core(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = l_Lean_Compiler_unFoldFns;
x_7 = l___private_init_lean_compiler_constfolding_1__alistFind___main___rarg(x_3, x_6);
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; 
lean::dec(x_2);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_14 = lean::box(x_0);
x_15 = lean::apply_2(x_11, x_14, x_2);
return x_15;
}
}
default:
{
obj* x_18; 
lean::dec(x_1);
lean::dec(x_2);
x_18 = lean::box(0);
return x_18;
}
}
}
}
}
obj* l_Lean_Compiler_foldUnOp___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = lean::fold_un_op_core(x_3, x_1, x_2);
return x_4;
}
}
obj* initialize_init_lean_expr(obj*);
obj* initialize_init_platform(obj*);
obj* initialize_init_lean_compiler_util(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_constfolding(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_platform(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_util(w);
 l_Lean_Compiler_mkUIntTypeName___closed__1 = _init_l_Lean_Compiler_mkUIntTypeName___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkUIntTypeName___closed__1);
 l_Lean_Compiler_numScalarTypes = _init_l_Lean_Compiler_numScalarTypes();
lean::mark_persistent(l_Lean_Compiler_numScalarTypes);
 l_Lean_Compiler_mkUInt32Lit___closed__1 = _init_l_Lean_Compiler_mkUInt32Lit___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkUInt32Lit___closed__1);
 l_Lean_Compiler_foldUIntAdd___closed__1 = _init_l_Lean_Compiler_foldUIntAdd___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldUIntAdd___closed__1);
 l_Lean_Compiler_foldUIntMul___closed__1 = _init_l_Lean_Compiler_foldUIntMul___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldUIntMul___closed__1);
 l_Lean_Compiler_foldUIntDiv___closed__1 = _init_l_Lean_Compiler_foldUIntDiv___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldUIntDiv___closed__1);
 l_Lean_Compiler_foldUIntMod___closed__1 = _init_l_Lean_Compiler_foldUIntMod___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldUIntMod___closed__1);
 l_Lean_Compiler_foldUIntSub___closed__1 = _init_l_Lean_Compiler_foldUIntSub___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldUIntSub___closed__1);
 l_Lean_Compiler_preUIntBinFoldFns = _init_l_Lean_Compiler_preUIntBinFoldFns();
lean::mark_persistent(l_Lean_Compiler_preUIntBinFoldFns);
 l_Lean_Compiler_uintBinFoldFns = _init_l_Lean_Compiler_uintBinFoldFns();
lean::mark_persistent(l_Lean_Compiler_uintBinFoldFns);
 l_Lean_Compiler_foldNatAdd___rarg___closed__1 = _init_l_Lean_Compiler_foldNatAdd___rarg___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatAdd___rarg___closed__1);
 l_Lean_Compiler_foldNatMul___rarg___closed__1 = _init_l_Lean_Compiler_foldNatMul___rarg___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatMul___rarg___closed__1);
 l_Lean_Compiler_foldNatDiv___rarg___closed__1 = _init_l_Lean_Compiler_foldNatDiv___rarg___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatDiv___rarg___closed__1);
 l_Lean_Compiler_foldNatMod___rarg___closed__1 = _init_l_Lean_Compiler_foldNatMod___rarg___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatMod___rarg___closed__1);
 l_Lean_Compiler_mkNatEq___closed__1 = _init_l_Lean_Compiler_mkNatEq___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkNatEq___closed__1);
 l_Lean_Compiler_mkNatLt___closed__1 = _init_l_Lean_Compiler_mkNatLt___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkNatLt___closed__1);
 l_Lean_Compiler_mkNatLe___closed__1 = _init_l_Lean_Compiler_mkNatLe___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkNatLe___closed__1);
 l_Lean_Compiler_toDecidableExpr___closed__1 = _init_l_Lean_Compiler_toDecidableExpr___closed__1();
lean::mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__1);
 l_Lean_Compiler_toDecidableExpr___closed__2 = _init_l_Lean_Compiler_toDecidableExpr___closed__2();
lean::mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__2);
 l_Lean_Compiler_foldNatDecEq___closed__1 = _init_l_Lean_Compiler_foldNatDecEq___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatDecEq___closed__1);
 l_Lean_Compiler_foldNatDecEq___closed__2 = _init_l_Lean_Compiler_foldNatDecEq___closed__2();
lean::mark_persistent(l_Lean_Compiler_foldNatDecEq___closed__2);
 l_Lean_Compiler_foldNatDecLt___closed__1 = _init_l_Lean_Compiler_foldNatDecLt___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatDecLt___closed__1);
 l_Lean_Compiler_foldNatDecLt___closed__2 = _init_l_Lean_Compiler_foldNatDecLt___closed__2();
lean::mark_persistent(l_Lean_Compiler_foldNatDecLt___closed__2);
 l_Lean_Compiler_foldNatDecLe___closed__1 = _init_l_Lean_Compiler_foldNatDecLe___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldNatDecLe___closed__1);
 l_Lean_Compiler_foldNatDecLe___closed__2 = _init_l_Lean_Compiler_foldNatDecLe___closed__2();
lean::mark_persistent(l_Lean_Compiler_foldNatDecLe___closed__2);
 l_Lean_Compiler_natFoldFns = _init_l_Lean_Compiler_natFoldFns();
lean::mark_persistent(l_Lean_Compiler_natFoldFns);
 l_Lean_Compiler_binFoldFns = _init_l_Lean_Compiler_binFoldFns();
lean::mark_persistent(l_Lean_Compiler_binFoldFns);
 l_Lean_Compiler_foldCharOfNat___closed__1 = _init_l_Lean_Compiler_foldCharOfNat___closed__1();
lean::mark_persistent(l_Lean_Compiler_foldCharOfNat___closed__1);
 l_Lean_Compiler_unFoldFns = _init_l_Lean_Compiler_unFoldFns();
lean::mark_persistent(l_Lean_Compiler_unFoldFns);
return w;
}
