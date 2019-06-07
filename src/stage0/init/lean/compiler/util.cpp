// Lean compiler output
// Module: init.lean.compiler.util
// Imports: init.lean.expr
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
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_HasAndthen;
obj* l_Lean_Compiler_atMostOnce_seq(obj*, obj*, obj*);
uint8 l_String_isPrefixOf(obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
namespace lean {
uint8 at_most_once_core(obj*, obj*);
}
obj* l_Lean_Compiler_atMostOnce_visit___boxed(obj*, obj*, obj*);
uint8 l_Lean_Compiler_isEagerLambdaLiftingName___main(obj*);
obj* l_Lean_Compiler_atMostOnce_visit___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visitFVar___main(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkLcProof(obj*);
obj* l_Nat_repr(obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Compiler_objectType;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Compiler_atMostOnce___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visit___main(obj*, obj*, obj*);
obj* l_Lean_Compiler_atMostOnce___boxed(obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visit(obj*, obj*, obj*);
obj* l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1;
obj* l_Lean_Compiler_atMostOnce_visitFVar(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
obj* l_Lean_Compiler_voidType;
obj* l_Lean_Compiler_atMostOnce_skip(obj*);
obj* l_Lean_Compiler_atMostOnce_skip___boxed(obj*);
namespace lean {
uint8 is_eager_lambda_lifting_name_core(obj*);
}
obj* l_Lean_Compiler_mkLcProof___closed__1;
obj* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(obj*);
namespace lean {
obj* mk_eager_lambda_lifting_name_core(obj*, obj*);
}
obj* l_Lean_Compiler_neutralExpr;
obj* l_Lean_Compiler_atMostOnce_visitFVar___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_unreachableExpr;
obj* l_Lean_Compiler_atMostOnce_visitFVar___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_isEagerLambdaLiftingName___main___boxed(obj*);
obj* _init_l_Lean_Compiler_neutralExpr() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_neutral");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Compiler_unreachableExpr() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_unreachable");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Compiler_objectType() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_obj");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Compiler_voidType() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_void");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("lcProof");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_3, x_4);
return x_5;
}
}
obj* l_Lean_Compiler_mkLcProof(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_mkLcProof___closed__1;
x_3 = lean_expr_mk_app(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Compiler_atMostOnce_seq(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_4, 1);
if (x_5 == 0)
{
lean::dec(x_2);
return x_4;
}
else
{
obj* x_6; 
x_6 = lean::apply_1(x_2, x_4);
return x_6;
}
}
}
obj* _init_l_Lean_Compiler_atMostOnce_HasAndthen() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_atMostOnce_seq), 3, 0);
return x_1;
}
}
obj* l_Lean_Compiler_atMostOnce_skip(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Compiler_atMostOnce_skip___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_atMostOnce_skip(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_3, 0);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_6 == 0)
{
lean::cnstr_set_scalar(x_3, 0, x_6);
return x_3;
}
else
{
uint8 x_7; 
x_7 = lean_name_dec_eq(x_1, x_2);
lean::cnstr_set_scalar(x_3, 0, x_7);
return x_3;
}
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_3, 1);
lean::dec(x_3);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_9, 0, x_8);
lean::cnstr_set_scalar(x_9, 1, x_8);
return x_9;
}
else
{
uint8 x_10; obj* x_11; 
x_10 = lean_name_dec_eq(x_1, x_2);
x_11 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_11, 0, x_10);
lean::cnstr_set_scalar(x_11, 1, x_8);
return x_11;
}
}
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_12 == 0)
{
return x_3;
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = lean_name_dec_eq(x_1, x_2);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 1;
lean::cnstr_set_scalar(x_3, 0, x_12);
lean::cnstr_set_scalar(x_3, 1, x_15);
return x_3;
}
else
{
uint8 x_16; 
x_16 = 0;
lean::cnstr_set_scalar(x_3, 0, x_12);
lean::cnstr_set_scalar(x_3, 1, x_16);
return x_3;
}
}
else
{
uint8 x_17; 
lean::dec(x_3);
x_17 = lean_name_dec_eq(x_1, x_2);
if (x_17 == 0)
{
uint8 x_18; obj* x_19; 
x_18 = 1;
x_19 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_19, 0, x_12);
lean::cnstr_set_scalar(x_19, 1, x_18);
return x_19;
}
else
{
uint8 x_20; obj* x_21; 
x_20 = 0;
x_21 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_21, 0, x_12);
lean::cnstr_set_scalar(x_21, 1, x_20);
return x_21;
}
}
}
}
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visitFVar___main(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_3, 0);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_6 == 0)
{
lean::cnstr_set_scalar(x_3, 0, x_6);
return x_3;
}
else
{
uint8 x_7; 
x_7 = lean_name_dec_eq(x_1, x_2);
lean::cnstr_set_scalar(x_3, 0, x_7);
return x_3;
}
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_3, 1);
lean::dec(x_3);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_9, 0, x_8);
lean::cnstr_set_scalar(x_9, 1, x_8);
return x_9;
}
else
{
uint8 x_10; obj* x_11; 
x_10 = lean_name_dec_eq(x_1, x_2);
x_11 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_11, 0, x_10);
lean::cnstr_set_scalar(x_11, 1, x_8);
return x_11;
}
}
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_12 == 0)
{
return x_3;
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = lean_name_dec_eq(x_1, x_2);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 1;
lean::cnstr_set_scalar(x_3, 0, x_12);
lean::cnstr_set_scalar(x_3, 1, x_15);
return x_3;
}
else
{
uint8 x_16; 
x_16 = 0;
lean::cnstr_set_scalar(x_3, 0, x_12);
lean::cnstr_set_scalar(x_3, 1, x_16);
return x_3;
}
}
else
{
uint8 x_17; 
lean::dec(x_3);
x_17 = lean_name_dec_eq(x_1, x_2);
if (x_17 == 0)
{
uint8 x_18; obj* x_19; 
x_18 = 1;
x_19 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_19, 0, x_12);
lean::cnstr_set_scalar(x_19, 1, x_18);
return x_19;
}
else
{
uint8 x_20; obj* x_21; 
x_20 = 0;
x_21 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_21, 0, x_12);
lean::cnstr_set_scalar(x_21, 1, x_20);
return x_21;
}
}
}
}
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visitFVar(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Compiler_atMostOnce_visit___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_3, 0);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_6 == 0)
{
lean::cnstr_set_scalar(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean_name_dec_eq(x_7, x_1);
lean::cnstr_set_scalar(x_3, 0, x_8);
return x_3;
}
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_3, 1);
lean::dec(x_3);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_10, 0, x_9);
lean::cnstr_set_scalar(x_10, 1, x_9);
return x_10;
}
else
{
obj* x_11; uint8 x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean_name_dec_eq(x_11, x_1);
x_13 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_13, 0, x_12);
lean::cnstr_set_scalar(x_13, 1, x_9);
return x_13;
}
}
}
else
{
uint8 x_14; 
x_14 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_14 == 0)
{
return x_3;
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_3);
if (x_15 == 0)
{
obj* x_16; uint8 x_17; 
x_16 = lean::cnstr_get(x_2, 0);
x_17 = lean_name_dec_eq(x_16, x_1);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = 1;
lean::cnstr_set_scalar(x_3, 0, x_14);
lean::cnstr_set_scalar(x_3, 1, x_18);
return x_3;
}
else
{
uint8 x_19; 
x_19 = 0;
lean::cnstr_set_scalar(x_3, 0, x_14);
lean::cnstr_set_scalar(x_3, 1, x_19);
return x_3;
}
}
else
{
obj* x_20; uint8 x_21; 
lean::dec(x_3);
x_20 = lean::cnstr_get(x_2, 0);
x_21 = lean_name_dec_eq(x_20, x_1);
if (x_21 == 0)
{
uint8 x_22; obj* x_23; 
x_22 = 1;
x_23 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_23, 0, x_14);
lean::cnstr_set_scalar(x_23, 1, x_22);
return x_23;
}
else
{
uint8 x_24; obj* x_25; 
x_24 = 0;
x_25 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_25, 0, x_14);
lean::cnstr_set_scalar(x_25, 1, x_24);
return x_25;
}
}
}
}
}
case 5:
{
obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_26 = lean::cnstr_get(x_2, 0);
x_27 = lean::cnstr_get(x_2, 1);
x_28 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_27, x_3);
x_29 = lean::cnstr_get_scalar<uint8>(x_28, 1);
if (x_29 == 0)
{
return x_28;
}
else
{
x_2 = x_26;
x_3 = x_28;
goto _start;
}
}
case 6:
{
obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_31 = lean::cnstr_get(x_2, 1);
x_32 = lean::cnstr_get(x_2, 2);
x_33 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_31, x_3);
x_34 = lean::cnstr_get_scalar<uint8>(x_33, 1);
if (x_34 == 0)
{
return x_33;
}
else
{
x_2 = x_32;
x_3 = x_33;
goto _start;
}
}
case 7:
{
obj* x_36; obj* x_37; obj* x_38; uint8 x_39; 
x_36 = lean::cnstr_get(x_2, 1);
x_37 = lean::cnstr_get(x_2, 2);
x_38 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_36, x_3);
x_39 = lean::cnstr_get_scalar<uint8>(x_38, 1);
if (x_39 == 0)
{
return x_38;
}
else
{
x_2 = x_37;
x_3 = x_38;
goto _start;
}
}
case 8:
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; 
x_41 = lean::cnstr_get(x_2, 1);
x_42 = lean::cnstr_get(x_2, 2);
x_43 = lean::cnstr_get(x_2, 3);
x_44 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_41, x_3);
x_45 = lean::cnstr_get_scalar<uint8>(x_44, 1);
if (x_45 == 0)
{
return x_44;
}
else
{
obj* x_46; uint8 x_47; 
x_46 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_42, x_44);
x_47 = lean::cnstr_get_scalar<uint8>(x_46, 1);
if (x_47 == 0)
{
return x_46;
}
else
{
x_2 = x_43;
x_3 = x_46;
goto _start;
}
}
}
case 10:
{
obj* x_49; 
x_49 = lean::cnstr_get(x_2, 1);
x_2 = x_49;
goto _start;
}
case 11:
{
obj* x_51; 
x_51 = lean::cnstr_get(x_2, 2);
x_2 = x_51;
goto _start;
}
default: 
{
return x_3;
}
}
}
}
obj* l_Lean_Compiler_atMostOnce_visit___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Compiler_atMostOnce_visit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Compiler_atMostOnce_visit___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Compiler_atMostOnce___closed__1() {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_3, 0, x_1);
lean::cnstr_set_scalar(x_3, 1, x_2);
return x_3;
}
}
namespace lean {
uint8 at_most_once_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = l_Lean_Compiler_atMostOnce___closed__1;
x_4 = l_Lean_Compiler_atMostOnce_visit___main(x_2, x_1, x_3);
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::cnstr_get_scalar<uint8>(x_4, 1);
lean::dec(x_4);
return x_5;
}
}
}
obj* l_Lean_Compiler_atMostOnce___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::at_most_once_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_elambda_");
return x_1;
}
}
namespace lean {
obj* mk_eager_lambda_lifting_name_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_6 = lean_name_mk_string(x_1, x_5);
return x_6;
}
}
}
obj* _init_l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_elambda");
return x_1;
}
}
uint8 l_Lean_Compiler_isEagerLambdaLiftingName___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1;
x_6 = l_String_isPrefixOf(x_5, x_4);
if (x_6 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
default: 
{
obj* x_9; 
x_9 = lean::cnstr_get(x_1, 0);
x_1 = x_9;
goto _start;
}
}
}
}
obj* l_Lean_Compiler_isEagerLambdaLiftingName___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Compiler_isEagerLambdaLiftingName___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
namespace lean {
uint8 is_eager_lambda_lifting_name_core(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Compiler_isEagerLambdaLiftingName___main(x_1);
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::is_eager_lambda_lifting_name_core(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* initialize_init_lean_expr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_util(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_neutralExpr = _init_l_Lean_Compiler_neutralExpr();
lean::mark_persistent(l_Lean_Compiler_neutralExpr);
l_Lean_Compiler_unreachableExpr = _init_l_Lean_Compiler_unreachableExpr();
lean::mark_persistent(l_Lean_Compiler_unreachableExpr);
l_Lean_Compiler_objectType = _init_l_Lean_Compiler_objectType();
lean::mark_persistent(l_Lean_Compiler_objectType);
l_Lean_Compiler_voidType = _init_l_Lean_Compiler_voidType();
lean::mark_persistent(l_Lean_Compiler_voidType);
l_Lean_Compiler_mkLcProof___closed__1 = _init_l_Lean_Compiler_mkLcProof___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkLcProof___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "mkLcProof"), 1, l_Lean_Compiler_mkLcProof);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "atMostOnce"), "seq"), 3, l_Lean_Compiler_atMostOnce_seq);
l_Lean_Compiler_atMostOnce_HasAndthen = _init_l_Lean_Compiler_atMostOnce_HasAndthen();
lean::mark_persistent(l_Lean_Compiler_atMostOnce_HasAndthen);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "atMostOnce"), "skip"), 1, l_Lean_Compiler_atMostOnce_skip___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "atMostOnce"), "visitFVar"), 3, l_Lean_Compiler_atMostOnce_visitFVar___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "atMostOnce"), "visit"), 3, l_Lean_Compiler_atMostOnce_visit___boxed);
l_Lean_Compiler_atMostOnce___closed__1 = _init_l_Lean_Compiler_atMostOnce___closed__1();
lean::mark_persistent(l_Lean_Compiler_atMostOnce___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "atMostOnce"), 2, l_Lean_Compiler_atMostOnce___boxed);
l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "mkEagerLambdaLiftingName"), 2, lean::mk_eager_lambda_lifting_name_core);
l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1();
lean::mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Compiler"), "isEagerLambdaLiftingName"), 1, l_Lean_Compiler_isEagerLambdaLiftingName___boxed);
return w;
}
