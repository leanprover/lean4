// Lean compiler output
// Module: init.lean.compiler.ir.checker
// Imports: init.lean.compiler.ir.basic init.control.reader
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
obj* l_Lean_IR_Checker_checkExpr___main(obj*, obj*);
uint8 l_Lean_IR_Context_isLocalVar(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_Context_isParam(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
obj* l_Lean_IR_Checker_checkFnBody___main___closed__1;
obj* l_Lean_IR_Checker_checkExpr___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkDecl(obj*, obj*);
obj* l_Lean_IR_Decl_check___closed__1;
uint8 l_Lean_IR_Context_contains(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main___closed__2;
obj* l_Lean_IR_Context_addDecl(obj*, obj*);
obj* l_Lean_IR_Context_addParam(obj*, obj*);
obj* l_Lean_IR_Checker_checkDecl___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_Checker_withParams(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkJP(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_Decl_id___main(obj*);
extern obj* l_Char_HasRepr___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkVar___closed__2;
obj* l_Lean_IR_Checker_checkArg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_Checker_checkExpr___main___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkArgs___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkVar(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
obj* l_Lean_IR_Checker_checkVar___closed__1;
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(obj*, obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_Checker_checkArgs(obj*, obj*);
uint8 l_Lean_IR_Context_isJP(obj*, obj*);
obj* l_Lean_IR_Checker_withParams___boxed(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main(obj*, obj*);
obj* l_Lean_IR_Checker_checkJP___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_check___closed__2;
obj* l_Lean_IR_Checker_checkExpr(obj*, obj*);
obj* l_Lean_IR_Decl_check(obj*, obj*);
obj* _init_l_Lean_IR_Checker_checkVar___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown variable '");
return x_0;
}
}
obj* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_Checker_checkVar(obj* x_0, obj* x_1) {
_start:
{
uint8 x_3; 
lean::inc(x_1);
x_3 = l_Lean_IR_Context_isLocalVar(x_1, x_0);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = l_Lean_IR_Context_isParam(x_1, x_0);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = l_Nat_repr(x_0);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_9 = l_Lean_IR_Checker_checkVar___closed__1;
x_10 = lean::string_append(x_9, x_7);
lean::dec(x_7);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_10, x_12);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_16; 
lean::dec(x_0);
x_16 = l_Lean_IR_Checker_checkVar___closed__2;
return x_16;
}
}
else
{
obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
x_19 = l_Lean_IR_Checker_checkVar___closed__2;
return x_19;
}
}
}
obj* _init_l_Lean_IR_Checker_checkJP___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown join point '");
return x_0;
}
}
obj* l_Lean_IR_Checker_checkJP(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_Context_isJP(x_1, x_0);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_Nat_repr(x_0);
x_4 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_7 = l_Lean_IR_Checker_checkJP___closed__1;
x_8 = lean::string_append(x_7, x_5);
lean::dec(x_5);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_14; 
lean::dec(x_0);
x_14 = l_Lean_IR_Checker_checkVar___closed__2;
return x_14;
}
}
}
obj* l_Lean_IR_Checker_checkArg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_IR_Checker_checkVar(x_2, x_1);
return x_5;
}
else
{
obj* x_7; 
lean::dec(x_1);
x_7 = l_Lean_IR_Checker_checkVar___closed__2;
return x_7;
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_8; 
lean::dec(x_1);
lean::dec(x_2);
x_8 = l_Lean_IR_Checker_checkVar___closed__2;
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_14; 
x_9 = lean::array_fget(x_0, x_1);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
lean::inc(x_2);
x_14 = l_Lean_IR_Checker_checkArg(x_9, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_11);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_19 = x_14;
} else {
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
return x_20;
}
else
{
lean::dec(x_14);
x_1 = x_11;
goto _start;
}
}
}
}
obj* l_Lean_IR_Checker_checkArgs(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkArgs___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkArgs(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_Checker_checkExpr___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkVar___closed__2;
return x_2;
}
}
obj* l_Lean_IR_Checker_checkExpr___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkExpr___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_Checker_checkExpr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkVar___closed__2;
return x_2;
}
}
obj* l_Lean_IR_Checker_checkExpr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkExpr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("invalid parameter declaration, shadowing is not allowed");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; uint8 x_17; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::inc(x_3);
x_17 = l_Lean_IR_Context_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_Context_addParam(x_3, x_10);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_10);
x_24 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_24;
}
}
}
}
obj* l_Lean_IR_Checker_withParams(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_5 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_0, x_0, x_3, x_2, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::apply_1(x_1, x_12);
return x_15;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_IR_Checker_withParams___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_withParams(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; uint8 x_17; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::inc(x_3);
x_17 = l_Lean_IR_Context_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_Context_addParam(x_3, x_10);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_10);
x_24 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_24;
}
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_8; 
lean::dec(x_1);
lean::dec(x_2);
x_8 = l_Lean_IR_Checker_checkVar___closed__2;
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; 
x_9 = lean::array_fget(x_0, x_1);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_13 = l_Lean_IR_AltCore_body___main(x_9);
lean::dec(x_9);
lean::inc(x_2);
x_16 = l_Lean_IR_Checker_checkFnBody___main(x_13, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_11);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_21 = x_16;
} else {
 lean::inc(x_19);
 lean::dec(x_16);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
return x_22;
}
else
{
lean::dec(x_16);
x_1 = x_11;
goto _start;
}
}
}
}
obj* _init_l_Lean_IR_Checker_checkFnBody___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("invalid variable declaration, shadowing is not allowed");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_Checker_checkFnBody___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("invalid join point declaration, shadowing is not allowed");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_Checker_checkFnBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_4; uint8 x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::inc(x_1);
x_7 = l_Lean_IR_Context_contains(x_1, x_2);
lean::dec(x_2);
if (x_7 == 0)
{
obj* x_9; 
x_9 = l_Lean_IR_Context_addDecl(x_1, x_0);
x_0 = x_4;
x_1 = x_9;
goto _start;
}
else
{
obj* x_14; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_14 = l_Lean_IR_Checker_checkFnBody___main___closed__1;
return x_14;
}
}
case 1:
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 3);
lean::inc(x_21);
x_23 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_25 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_17, x_17, x_23, x_1, x_1);
lean::dec(x_17);
if (lean::obj_tag(x_25) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
return x_35;
}
else
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_25, 0);
lean::inc(x_36);
lean::dec(x_25);
x_39 = l_Lean_IR_Checker_checkFnBody___main(x_19, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_21);
x_44 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
uint8 x_50; 
lean::dec(x_39);
lean::inc(x_1);
x_50 = l_Lean_IR_Context_contains(x_1, x_15);
lean::dec(x_15);
if (x_50 == 0)
{
obj* x_52; 
x_52 = l_Lean_IR_Context_addDecl(x_1, x_0);
x_0 = x_21;
x_1 = x_52;
goto _start;
}
else
{
obj* x_57; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_21);
x_57 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_57;
}
}
}
}
case 2:
{
obj* x_58; obj* x_60; obj* x_62; obj* x_66; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_0, 2);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_0, 3);
lean::inc(x_62);
lean::dec(x_0);
lean::inc(x_1);
x_66 = l_Lean_IR_Checker_checkVar(x_58, x_1);
if (lean::obj_tag(x_66) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_60);
lean::dec(x_62);
x_70 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_72 = x_66;
} else {
 lean::inc(x_70);
 lean::dec(x_66);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
return x_73;
}
else
{
obj* x_76; 
lean::dec(x_66);
lean::inc(x_1);
x_76 = l_Lean_IR_Checker_checkVar(x_60, x_1);
if (lean::obj_tag(x_76) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_1);
lean::dec(x_62);
x_79 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_81 = x_76;
} else {
 lean::inc(x_79);
 lean::dec(x_76);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
return x_82;
}
else
{
lean::dec(x_76);
x_0 = x_62;
goto _start;
}
}
}
case 3:
{
obj* x_85; obj* x_87; obj* x_89; obj* x_93; 
x_85 = lean::cnstr_get(x_0, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_0, 2);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_0, 3);
lean::inc(x_89);
lean::dec(x_0);
lean::inc(x_1);
x_93 = l_Lean_IR_Checker_checkVar(x_85, x_1);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_1);
lean::dec(x_89);
lean::dec(x_87);
x_97 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_99 = x_93;
} else {
 lean::inc(x_97);
 lean::dec(x_93);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_103; 
lean::dec(x_93);
lean::inc(x_1);
x_103 = l_Lean_IR_Checker_checkVar(x_87, x_1);
if (lean::obj_tag(x_103) == 0)
{
obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_1);
lean::dec(x_89);
x_106 = lean::cnstr_get(x_103, 0);
if (lean::is_exclusive(x_103)) {
 x_108 = x_103;
} else {
 lean::inc(x_106);
 lean::dec(x_103);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
return x_109;
}
else
{
lean::dec(x_103);
x_0 = x_89;
goto _start;
}
}
}
case 4:
{
obj* x_112; obj* x_114; obj* x_116; obj* x_120; 
x_112 = lean::cnstr_get(x_0, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_0, 3);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_0, 4);
lean::inc(x_116);
lean::dec(x_0);
lean::inc(x_1);
x_120 = l_Lean_IR_Checker_checkVar(x_112, x_1);
if (lean::obj_tag(x_120) == 0)
{
obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_1);
lean::dec(x_116);
lean::dec(x_114);
x_124 = lean::cnstr_get(x_120, 0);
if (lean::is_exclusive(x_120)) {
 x_126 = x_120;
} else {
 lean::inc(x_124);
 lean::dec(x_120);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
return x_127;
}
else
{
obj* x_130; 
lean::dec(x_120);
lean::inc(x_1);
x_130 = l_Lean_IR_Checker_checkVar(x_114, x_1);
if (lean::obj_tag(x_130) == 0)
{
obj* x_133; obj* x_135; obj* x_136; 
lean::dec(x_1);
lean::dec(x_116);
x_133 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_135 = x_130;
} else {
 lean::inc(x_133);
 lean::dec(x_130);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_133);
return x_136;
}
else
{
lean::dec(x_130);
x_0 = x_116;
goto _start;
}
}
}
case 7:
{
obj* x_139; obj* x_141; obj* x_145; 
x_139 = lean::cnstr_get(x_0, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_0, 2);
lean::inc(x_141);
lean::dec(x_0);
lean::inc(x_1);
x_145 = l_Lean_IR_Checker_checkVar(x_139, x_1);
if (lean::obj_tag(x_145) == 0)
{
obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_1);
lean::dec(x_141);
x_148 = lean::cnstr_get(x_145, 0);
if (lean::is_exclusive(x_145)) {
 x_150 = x_145;
} else {
 lean::inc(x_148);
 lean::dec(x_145);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
return x_151;
}
else
{
lean::dec(x_145);
x_0 = x_141;
goto _start;
}
}
case 8:
{
obj* x_154; 
x_154 = lean::cnstr_get(x_0, 1);
lean::inc(x_154);
lean::dec(x_0);
x_0 = x_154;
goto _start;
}
case 9:
{
obj* x_158; obj* x_160; obj* x_164; 
x_158 = lean::cnstr_get(x_0, 1);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_0, 2);
lean::inc(x_160);
lean::dec(x_0);
lean::inc(x_1);
x_164 = l_Lean_IR_Checker_checkVar(x_158, x_1);
if (lean::obj_tag(x_164) == 0)
{
obj* x_167; obj* x_169; obj* x_170; 
lean::dec(x_160);
lean::dec(x_1);
x_167 = lean::cnstr_get(x_164, 0);
if (lean::is_exclusive(x_164)) {
 x_169 = x_164;
} else {
 lean::inc(x_167);
 lean::dec(x_164);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
return x_170;
}
else
{
obj* x_172; obj* x_173; 
lean::dec(x_164);
x_172 = lean::mk_nat_obj(0ul);
x_173 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_160, x_172, x_1);
lean::dec(x_160);
return x_173;
}
}
case 10:
{
obj* x_175; obj* x_178; 
x_175 = lean::cnstr_get(x_0, 0);
lean::inc(x_175);
lean::dec(x_0);
x_178 = l_Lean_IR_Checker_checkArg(x_175, x_1);
return x_178;
}
case 11:
{
obj* x_179; obj* x_181; obj* x_185; 
x_179 = lean::cnstr_get(x_0, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_0, 1);
lean::inc(x_181);
lean::dec(x_0);
lean::inc(x_1);
x_185 = l_Lean_IR_Checker_checkJP(x_179, x_1);
if (lean::obj_tag(x_185) == 0)
{
obj* x_188; obj* x_190; obj* x_191; 
lean::dec(x_181);
lean::dec(x_1);
x_188 = lean::cnstr_get(x_185, 0);
if (lean::is_exclusive(x_185)) {
 x_190 = x_185;
} else {
 lean::inc(x_188);
 lean::dec(x_185);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_188);
return x_191;
}
else
{
obj* x_193; obj* x_194; 
lean::dec(x_185);
x_193 = lean::mk_nat_obj(0ul);
x_194 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_181, x_193, x_1);
lean::dec(x_181);
return x_194;
}
}
case 12:
{
obj* x_197; 
lean::dec(x_1);
x_197 = l_Lean_IR_Checker_checkVar___closed__2;
return x_197;
}
default:
{
obj* x_198; obj* x_200; obj* x_204; 
x_198 = lean::cnstr_get(x_0, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_0, 2);
lean::inc(x_200);
lean::dec(x_0);
lean::inc(x_1);
x_204 = l_Lean_IR_Checker_checkVar(x_198, x_1);
if (lean::obj_tag(x_204) == 0)
{
obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_200);
lean::dec(x_1);
x_207 = lean::cnstr_get(x_204, 0);
if (lean::is_exclusive(x_204)) {
 x_209 = x_204;
} else {
 lean::inc(x_207);
 lean::dec(x_204);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_207);
return x_210;
}
else
{
lean::dec(x_204);
x_0 = x_200;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; uint8 x_17; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::inc(x_3);
x_17 = l_Lean_IR_Context_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_Context_addParam(x_3, x_10);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_10);
x_24 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_24;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; uint8 x_17; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::inc(x_3);
x_17 = l_Lean_IR_Context_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_Context_addParam(x_3, x_10);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_10);
x_24 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_24;
}
}
}
}
obj* l_Lean_IR_Checker_checkDecl___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_9 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(x_2, x_2, x_7, x_1, x_1);
lean::dec(x_1);
lean::dec(x_2);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_4);
x_13 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_9, 0);
lean::inc(x_17);
lean::dec(x_9);
x_20 = l_Lean_IR_Checker_checkFnBody___main(x_4, x_17);
return x_20;
}
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_28 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(x_21, x_21, x_26, x_1, x_1);
lean::dec(x_1);
lean::dec(x_21);
if (lean::obj_tag(x_28) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_25);
x_32 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_34 = x_28;
} else {
 lean::inc(x_32);
 lean::dec(x_28);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
return x_35;
}
else
{
lean::dec(x_28);
return x_25;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_IR_Checker_checkDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_checkDecl___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_Decl_check___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_Decl_check___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("IR check failed at '");
return x_0;
}
}
obj* l_Lean_IR_Decl_check(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_Lean_IR_Decl_check___closed__1;
lean::inc(x_0);
x_4 = l_Lean_IR_Checker_checkDecl___main(x_0, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_8 = x_1;
} else {
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_Decl_id___main(x_0);
lean::dec(x_0);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_9);
x_13 = l_Lean_IR_Decl_check___closed__2;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean::string_append(x_14, x_16);
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
return x_18;
}
else
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_4);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_23 = x_1;
} else {
 lean::inc(x_21);
 lean::dec(x_1);
 x_23 = lean::box(0);
}
x_24 = lean::box(0);
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_21);
return x_25;
}
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_control_reader(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_checker(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
 l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
 l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
 l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1 = _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1();
lean::mark_persistent(l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1);
 l_Lean_IR_Checker_checkFnBody___main___closed__1 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__1);
 l_Lean_IR_Checker_checkFnBody___main___closed__2 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__2);
 l_Lean_IR_Decl_check___closed__1 = _init_l_Lean_IR_Decl_check___closed__1();
lean::mark_persistent(l_Lean_IR_Decl_check___closed__1);
 l_Lean_IR_Decl_check___closed__2 = _init_l_Lean_IR_Decl_check___closed__2();
lean::mark_persistent(l_Lean_IR_Decl_check___closed__2);
return w;
}
