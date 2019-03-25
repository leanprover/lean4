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
obj* l_Lean_Compiler_atMostOnce_seq(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
namespace lean {
uint8 at_most_once(obj*, obj*);
}
obj* l_Lean_Compiler_atMostOnce_visit___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visit___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visitFVar___main(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkLcProof(obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Compiler_objectType;
obj* l_Lean_Compiler_atMostOnce___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visit___main(obj*, obj*, obj*);
obj* l_Lean_Compiler_atMostOnce___boxed(obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visit(obj*, obj*, obj*);
obj* l_Lean_Compiler_atMostOnce_visitFVar(obj*, obj*, obj*);
obj* l_Lean_Compiler_voidType;
obj* l_Lean_Compiler_atMostOnce_skip(obj*);
obj* l_Lean_Compiler_atMostOnce_skip___boxed(obj*);
obj* l_Lean_Compiler_mkLcProof___closed__1;
obj* l_Lean_Compiler_neutralExpr;
obj* l_Lean_Compiler_atMostOnce_visitFVar___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_unreachableExpr;
obj* l_Lean_Compiler_atMostOnce_visitFVar___main___boxed(obj*, obj*, obj*);
obj* _init_l_Lean_Compiler_neutralExpr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_neutral");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_unreachableExpr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_unreachable");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_objectType() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_obj");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_voidType() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_void");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lcProof");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Compiler_mkLcProof(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Compiler_mkLcProof___closed__1;
x_2 = lean_expr_mk_app(x_1, x_0);
return x_2;
}
}
obj* l_Lean_Compiler_atMostOnce_seq(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_3, 1);
if (x_4 == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; 
x_6 = lean::apply_1(x_1, x_3);
return x_6;
}
}
}
obj* l_Lean_Compiler_atMostOnce_skip(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_Compiler_atMostOnce_skip___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_atMostOnce_skip(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = lean::cnstr_get_scalar<uint8>(x_2, 0);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, 1);
if (x_3 == 0)
{
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_5, 0, x_4);
x_6 = x_5;
lean::cnstr_set_scalar(x_6, 1, x_4);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean_name_dec_eq(x_0, x_1);
if (x_8 == 0)
{
uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = 0;
x_10 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_10, 0, x_9);
x_11 = x_10;
lean::cnstr_set_scalar(x_11, 1, x_4);
x_12 = x_11;
return x_12;
}
else
{
uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = 1;
x_14 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_14, 0, x_13);
x_15 = x_14;
lean::cnstr_set_scalar(x_15, 1, x_4);
x_16 = x_15;
return x_16;
}
}
}
else
{
if (x_4 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
uint8 x_18; 
x_18 = lean_name_dec_eq(x_0, x_1);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_19, 0, x_4);
x_20 = x_19;
lean::cnstr_set_scalar(x_20, 1, x_4);
x_21 = x_20;
return x_21;
}
else
{
uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = 0;
x_23 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_23, 0, x_4);
x_24 = x_23;
lean::cnstr_set_scalar(x_24, 1, x_22);
x_25 = x_24;
return x_25;
}
}
}
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_atMostOnce_visitFVar___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = lean::cnstr_get_scalar<uint8>(x_2, 0);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, 1);
if (x_3 == 0)
{
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_5, 0, x_4);
x_6 = x_5;
lean::cnstr_set_scalar(x_6, 1, x_4);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean_name_dec_eq(x_0, x_1);
if (x_8 == 0)
{
uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = 0;
x_10 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_10, 0, x_9);
x_11 = x_10;
lean::cnstr_set_scalar(x_11, 1, x_4);
x_12 = x_11;
return x_12;
}
else
{
uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = 1;
x_14 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_14, 0, x_13);
x_15 = x_14;
lean::cnstr_set_scalar(x_15, 1, x_4);
x_16 = x_15;
return x_16;
}
}
}
else
{
if (x_4 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
uint8 x_18; 
x_18 = lean_name_dec_eq(x_0, x_1);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_19, 0, x_4);
x_20 = x_19;
lean::cnstr_set_scalar(x_20, 1, x_4);
x_21 = x_20;
return x_21;
}
else
{
uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = 0;
x_23 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_23, 0, x_4);
x_24 = x_23;
lean::cnstr_set_scalar(x_24, 1, x_22);
x_25 = x_24;
return x_25;
}
}
}
}
}
obj* l_Lean_Compiler_atMostOnce_visitFVar___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_atMostOnce_visitFVar(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Compiler_atMostOnce_visit___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
uint8 x_3; uint8 x_4; 
x_3 = lean::cnstr_get_scalar<uint8>(x_2, 0);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, 1);
if (x_3 == 0)
{
lean::dec(x_2);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_6, 0, x_4);
x_7 = x_6;
lean::cnstr_set_scalar(x_7, 1, x_4);
x_8 = x_7;
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean_name_dec_eq(x_9, x_0);
if (x_10 == 0)
{
uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = 0;
x_12 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_12, 0, x_11);
x_13 = x_12;
lean::cnstr_set_scalar(x_13, 1, x_4);
x_14 = x_13;
return x_14;
}
else
{
uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = 1;
x_16 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_16, 0, x_15);
x_17 = x_16;
lean::cnstr_set_scalar(x_17, 1, x_4);
x_18 = x_17;
return x_18;
}
}
}
else
{
if (x_4 == 0)
{
return x_2;
}
else
{
obj* x_20; uint8 x_21; 
lean::dec(x_2);
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean_name_dec_eq(x_20, x_0);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_22, 0, x_4);
x_23 = x_22;
lean::cnstr_set_scalar(x_23, 1, x_4);
x_24 = x_23;
return x_24;
}
else
{
uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = 0;
x_26 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_26, 0, x_4);
x_27 = x_26;
lean::cnstr_set_scalar(x_27, 1, x_25);
x_28 = x_27;
return x_28;
}
}
}
}
case 5:
{
obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_29 = lean::cnstr_get(x_1, 0);
x_30 = lean::cnstr_get(x_1, 1);
x_31 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_30, x_2);
x_32 = lean::cnstr_get_scalar<uint8>(x_31, 1);
if (x_32 == 0)
{
return x_31;
}
else
{
x_1 = x_29;
x_2 = x_31;
goto _start;
}
}
case 6:
{
obj* x_34; obj* x_35; obj* x_36; uint8 x_37; 
x_34 = lean::cnstr_get(x_1, 1);
x_35 = lean::cnstr_get(x_1, 2);
x_36 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_34, x_2);
x_37 = lean::cnstr_get_scalar<uint8>(x_36, 1);
if (x_37 == 0)
{
return x_36;
}
else
{
x_1 = x_35;
x_2 = x_36;
goto _start;
}
}
case 7:
{
obj* x_39; obj* x_40; obj* x_41; uint8 x_42; 
x_39 = lean::cnstr_get(x_1, 1);
x_40 = lean::cnstr_get(x_1, 2);
x_41 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_39, x_2);
x_42 = lean::cnstr_get_scalar<uint8>(x_41, 1);
if (x_42 == 0)
{
return x_41;
}
else
{
x_1 = x_40;
x_2 = x_41;
goto _start;
}
}
case 8:
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_1, 1);
x_45 = lean::cnstr_get(x_1, 2);
x_46 = lean::cnstr_get(x_1, 3);
x_47 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_44, x_2);
x_48 = lean::cnstr_get_scalar<uint8>(x_47, 1);
if (x_48 == 0)
{
if (x_48 == 0)
{
return x_47;
}
else
{
x_1 = x_46;
x_2 = x_47;
goto _start;
}
}
else
{
obj* x_50; uint8 x_51; 
x_50 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_45, x_47);
x_51 = lean::cnstr_get_scalar<uint8>(x_50, 1);
if (x_51 == 0)
{
return x_50;
}
else
{
x_1 = x_46;
x_2 = x_50;
goto _start;
}
}
}
case 10:
{
obj* x_53; 
x_53 = lean::cnstr_get(x_1, 1);
x_1 = x_53;
goto _start;
}
case 11:
{
obj* x_55; 
x_55 = lean::cnstr_get(x_1, 2);
x_1 = x_55;
goto _start;
}
default:
{
return x_2;
}
}
}
}
obj* l_Lean_Compiler_atMostOnce_visit___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Compiler_atMostOnce_visit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_atMostOnce_visit___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Compiler_atMostOnce_visit___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_atMostOnce_visit(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Compiler_atMostOnce___closed__1() {
_start:
{
uint8 x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = 0;
x_1 = 1;
x_2 = lean::alloc_cnstr(0, 0, 2);
lean::cnstr_set_scalar(x_2, 0, x_0);
x_3 = x_2;
lean::cnstr_set_scalar(x_3, 1, x_1);
x_4 = x_3;
return x_4;
}
}
namespace lean {
uint8 at_most_once(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_6; 
x_2 = l_Lean_Compiler_atMostOnce___closed__1;
x_3 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_0, x_2);
lean::dec(x_0);
lean::dec(x_1);
x_6 = lean::cnstr_get_scalar<uint8>(x_3, 1);
lean::dec(x_3);
return x_6;
}
}
}
obj* l_Lean_Compiler_atMostOnce___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::at_most_once(x_0, x_1);
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
 l_Lean_Compiler_atMostOnce___closed__1 = _init_l_Lean_Compiler_atMostOnce___closed__1();
lean::mark_persistent(l_Lean_Compiler_atMostOnce___closed__1);
return w;
}
