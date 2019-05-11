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
obj* l_Lean_IR_Checker_checkType(uint8, obj*, obj*);
obj* l_Lean_IR_Checker_checkExpr___main(uint8, obj*, obj*);
uint8 l_Lean_IR_Context_isLocalVar(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_Context_addJP(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_Context_isParam(obj*, obj*);
obj* l_Lean_IR_Checker_checkScalarVar(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
obj* l_Lean_IR_Checker_checkFnBody___main___closed__1;
obj* l_Lean_IR_Checker_checkExpr___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkDecl(obj*, obj*);
obj* l_Lean_IR_Decl_check___closed__1;
uint8 l_Lean_IR_Context_contains(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main___closed__2;
uint8 l_Lean_IR_IRType_isObj___main(uint8);
obj* l_Lean_IR_Checker_checkType___closed__1;
obj* l_Lean_IR_Context_addParam(obj*, obj*);
obj* l_Lean_IR_Checker_checkDecl___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkType___boxed(obj*, obj*, obj*);
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
uint8 l_Lean_IR_CtorInfo_isScalar(obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkObjType___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkVar___closed__2;
obj* l_Lean_IR_Context_getType(obj*, obj*);
obj* l_Lean_IR_Checker_checkScalarType(uint8, obj*);
obj* l_Lean_IR_Checker_checkArg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_Checker_checkExpr___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkArgs___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkVar(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkVarType(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
obj* l_Lean_IR_Checker_checkVar___closed__1;
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(obj*, obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_Checker_checkArgs(obj*, obj*);
obj* l_Lean_IR_Context_addLocal(obj*, obj*, uint8, obj*);
uint8 l_Lean_IR_Context_isJP(obj*, obj*);
obj* l_Lean_IR_Checker_withParams___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkObjType(uint8, obj*);
obj* l_Lean_IR_Checker_checkScalarType___boxed(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main(obj*, obj*);
obj* l_Lean_IR_Checker_checkObjVar(obj*, obj*);
obj* l_Lean_IR_Checker_checkJP___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_check___closed__2;
uint8 l_Lean_IR_IRType_isScalar___main(uint8);
obj* l_Lean_IR_Checker_checkExpr(uint8, obj*, obj*);
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
obj* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unexpected type");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_Checker_checkType(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::box(x_0);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::unbox(x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = l_Lean_IR_Checker_checkType___closed__1;
return x_6;
}
else
{
obj* x_7; 
x_7 = l_Lean_IR_Checker_checkVar___closed__2;
return x_7;
}
}
}
obj* l_Lean_IR_Checker_checkType___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_IR_Checker_checkType(x_3, x_1, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkObjType(uint8 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_IRType_isObj___main(x_0);
if (x_2 == 0)
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkType___closed__1;
return x_3;
}
else
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkVar___closed__2;
return x_4;
}
}
}
obj* l_Lean_IR_Checker_checkObjType___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_Lean_IR_Checker_checkObjType(x_2, x_1);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkScalarType(uint8 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_IRType_isScalar___main(x_0);
if (x_2 == 0)
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkType___closed__1;
return x_3;
}
else
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkVar___closed__2;
return x_4;
}
}
}
obj* l_Lean_IR_Checker_checkScalarType___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_Lean_IR_Checker_checkScalarType(x_2, x_1);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkVarType(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Context_getType(x_2, x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_1);
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
obj* x_16; obj* x_19; uint8 x_20; 
lean::dec(x_0);
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::apply_1(x_1, x_16);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_21; 
x_21 = l_Lean_IR_Checker_checkType___closed__1;
return x_21;
}
else
{
obj* x_22; 
x_22 = l_Lean_IR_Checker_checkVar___closed__2;
return x_22;
}
}
}
}
obj* l_Lean_IR_Checker_checkObjVar(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Context_getType(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_Nat_repr(x_0);
x_4 = l_Lean_IR_VarId_HasToString___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_7 = l_Lean_IR_Checker_checkVar___closed__1;
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
obj* x_14; uint8 x_17; uint8 x_18; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::unbox(x_14);
x_18 = l_Lean_IR_IRType_isObj___main(x_17);
if (x_18 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_Checker_checkType___closed__1;
return x_19;
}
else
{
obj* x_20; 
x_20 = l_Lean_IR_Checker_checkVar___closed__2;
return x_20;
}
}
}
}
obj* l_Lean_IR_Checker_checkScalarVar(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Context_getType(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_Nat_repr(x_0);
x_4 = l_Lean_IR_VarId_HasToString___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_7 = l_Lean_IR_Checker_checkVar___closed__1;
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
obj* x_14; uint8 x_17; uint8 x_18; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::unbox(x_14);
x_18 = l_Lean_IR_IRType_isScalar___main(x_17);
if (x_18 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_Checker_checkType___closed__1;
return x_19;
}
else
{
obj* x_20; 
x_20 = l_Lean_IR_Checker_checkVar___closed__2;
return x_20;
}
}
}
}
obj* l_Lean_IR_Checker_checkExpr___main(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_5; uint8 x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_Lean_IR_CtorInfo_isScalar(x_3);
lean::dec(x_3);
if (x_8 == 0)
{
obj* x_10; 
x_10 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_5);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_15 = x_10;
} else {
 lean::inc(x_13);
 lean::dec(x_10);
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
obj* x_18; obj* x_19; 
lean::dec(x_10);
x_18 = lean::mk_nat_obj(0ul);
x_19 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_18, x_2);
lean::dec(x_5);
return x_19;
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::mk_nat_obj(0ul);
x_22 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_21, x_2);
lean::dec(x_5);
return x_22;
}
}
case 1:
{
obj* x_24; obj* x_28; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
lean::dec(x_1);
lean::inc(x_2);
x_28 = l_Lean_IR_Checker_checkObjVar(x_24, x_2);
if (lean::obj_tag(x_28) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_2);
x_30 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_32 = x_28;
} else {
 lean::inc(x_30);
 lean::dec(x_28);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_28);
x_35 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_35;
}
}
case 2:
{
obj* x_37; obj* x_39; obj* x_43; 
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
lean::dec(x_1);
lean::inc(x_2);
x_43 = l_Lean_IR_Checker_checkObjVar(x_37, x_2);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_39);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_51; obj* x_53; 
lean::dec(x_43);
x_51 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_53 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_39, x_51, x_2);
lean::dec(x_39);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; obj* x_58; obj* x_59; 
lean::dec(x_2);
x_56 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_58 = x_53;
} else {
 lean::inc(x_56);
 lean::dec(x_53);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_56);
return x_59;
}
else
{
obj* x_61; 
lean::dec(x_53);
x_61 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_61;
}
}
}
case 3:
{
obj* x_63; obj* x_67; 
x_63 = lean::cnstr_get(x_1, 1);
lean::inc(x_63);
lean::dec(x_1);
lean::inc(x_2);
x_67 = l_Lean_IR_Checker_checkObjVar(x_63, x_2);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_2);
x_69 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_71 = x_67;
} else {
 lean::inc(x_69);
 lean::dec(x_67);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
return x_72;
}
else
{
obj* x_74; 
lean::dec(x_67);
x_74 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_74;
}
}
case 4:
{
obj* x_76; obj* x_79; 
x_76 = lean::cnstr_get(x_1, 1);
lean::inc(x_76);
lean::dec(x_1);
x_79 = l_Lean_IR_Checker_checkObjVar(x_76, x_2);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
x_80 = lean::cnstr_get(x_79, 0);
if (lean::is_exclusive(x_79)) {
 x_82 = x_79;
} else {
 lean::inc(x_80);
 lean::dec(x_79);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
uint8 x_85; uint8 x_86; 
lean::dec(x_79);
x_85 = 5;
x_86 = l_Lean_IR_IRType_beq___main(x_0, x_85);
if (x_86 == 0)
{
obj* x_87; 
x_87 = l_Lean_IR_Checker_checkType___closed__1;
return x_87;
}
else
{
obj* x_88; 
x_88 = l_Lean_IR_Checker_checkVar___closed__2;
return x_88;
}
}
}
case 5:
{
obj* x_89; obj* x_93; 
x_89 = lean::cnstr_get(x_1, 2);
lean::inc(x_89);
lean::dec(x_1);
lean::inc(x_2);
x_93 = l_Lean_IR_Checker_checkObjVar(x_89, x_2);
if (lean::obj_tag(x_93) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_2);
x_95 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_97 = x_93;
} else {
 lean::inc(x_95);
 lean::dec(x_93);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
return x_98;
}
else
{
obj* x_100; 
lean::dec(x_93);
x_100 = l_Lean_IR_Checker_checkScalarType(x_0, x_2);
lean::dec(x_2);
return x_100;
}
}
case 6:
{
obj* x_102; obj* x_105; obj* x_106; 
x_102 = lean::cnstr_get(x_1, 1);
lean::inc(x_102);
lean::dec(x_1);
x_105 = lean::mk_nat_obj(0ul);
x_106 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_102, x_105, x_2);
lean::dec(x_102);
return x_106;
}
case 7:
{
obj* x_108; obj* x_111; 
x_108 = lean::cnstr_get(x_1, 1);
lean::inc(x_108);
lean::dec(x_1);
x_111 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
if (lean::obj_tag(x_111) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_108);
lean::dec(x_2);
x_114 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_116 = x_111;
} else {
 lean::inc(x_114);
 lean::dec(x_111);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
return x_117;
}
else
{
obj* x_119; obj* x_120; 
lean::dec(x_111);
x_119 = lean::mk_nat_obj(0ul);
x_120 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_108, x_119, x_2);
lean::dec(x_108);
return x_120;
}
}
case 8:
{
obj* x_122; obj* x_124; obj* x_128; 
x_122 = lean::cnstr_get(x_1, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_1, 1);
lean::inc(x_124);
lean::dec(x_1);
lean::inc(x_2);
x_128 = l_Lean_IR_Checker_checkObjVar(x_122, x_2);
if (lean::obj_tag(x_128) == 0)
{
obj* x_131; obj* x_133; obj* x_134; 
lean::dec(x_124);
lean::dec(x_2);
x_131 = lean::cnstr_get(x_128, 0);
if (lean::is_exclusive(x_128)) {
 x_133 = x_128;
} else {
 lean::inc(x_131);
 lean::dec(x_128);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
}
else
{
obj* x_136; obj* x_137; 
lean::dec(x_128);
x_136 = lean::mk_nat_obj(0ul);
x_137 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_124, x_136, x_2);
lean::dec(x_124);
return x_137;
}
}
case 9:
{
uint8 x_139; obj* x_140; obj* x_143; 
x_139 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_140 = lean::cnstr_get(x_1, 0);
lean::inc(x_140);
lean::dec(x_1);
x_143 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
if (lean::obj_tag(x_143) == 0)
{
obj* x_146; obj* x_148; obj* x_149; 
lean::dec(x_2);
lean::dec(x_140);
x_146 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_148 = x_143;
} else {
 lean::inc(x_146);
 lean::dec(x_143);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
return x_149;
}
else
{
obj* x_153; 
lean::dec(x_143);
lean::inc(x_2);
lean::inc(x_140);
x_153 = l_Lean_IR_Checker_checkScalarVar(x_140, x_2);
if (lean::obj_tag(x_153) == 0)
{
obj* x_156; obj* x_158; obj* x_159; 
lean::dec(x_2);
lean::dec(x_140);
x_156 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 x_158 = x_153;
} else {
 lean::inc(x_156);
 lean::dec(x_153);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_156);
return x_159;
}
else
{
obj* x_160; obj* x_161; 
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_160 = x_153;
} else {
 lean::dec(x_153);
 x_160 = lean::box(0);
}
x_161 = l_Lean_IR_Context_getType(x_2, x_140);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; obj* x_164; obj* x_166; obj* x_167; obj* x_169; obj* x_170; obj* x_171; 
x_162 = l_Nat_repr(x_140);
x_163 = l_Lean_IR_VarId_HasToString___closed__1;
x_164 = lean::string_append(x_163, x_162);
lean::dec(x_162);
x_166 = l_Lean_IR_Checker_checkVar___closed__1;
x_167 = lean::string_append(x_166, x_164);
lean::dec(x_164);
x_169 = l_Char_HasRepr___closed__1;
x_170 = lean::string_append(x_167, x_169);
if (lean::is_scalar(x_160)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_160;
 lean::cnstr_set_tag(x_160, 0);
}
lean::cnstr_set(x_171, 0, x_170);
return x_171;
}
else
{
obj* x_174; uint8 x_177; uint8 x_178; 
lean::dec(x_140);
lean::dec(x_160);
x_174 = lean::cnstr_get(x_161, 0);
lean::inc(x_174);
lean::dec(x_161);
x_177 = lean::unbox(x_174);
x_178 = l_Lean_IR_IRType_beq___main(x_177, x_139);
if (x_178 == 0)
{
obj* x_179; 
x_179 = l_Lean_IR_Checker_checkType___closed__1;
return x_179;
}
else
{
obj* x_180; 
x_180 = l_Lean_IR_Checker_checkVar___closed__2;
return x_180;
}
}
}
}
}
case 10:
{
obj* x_181; obj* x_184; 
x_181 = lean::cnstr_get(x_1, 0);
lean::inc(x_181);
lean::dec(x_1);
x_184 = l_Lean_IR_Checker_checkScalarType(x_0, x_2);
if (lean::obj_tag(x_184) == 0)
{
obj* x_187; obj* x_189; obj* x_190; 
lean::dec(x_181);
lean::dec(x_2);
x_187 = lean::cnstr_get(x_184, 0);
if (lean::is_exclusive(x_184)) {
 x_189 = x_184;
} else {
 lean::inc(x_187);
 lean::dec(x_184);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
return x_190;
}
else
{
obj* x_192; 
lean::dec(x_184);
x_192 = l_Lean_IR_Checker_checkObjVar(x_181, x_2);
return x_192;
}
}
case 11:
{
obj* x_193; 
x_193 = lean::cnstr_get(x_1, 0);
lean::inc(x_193);
lean::dec(x_1);
if (lean::obj_tag(x_193) == 0)
{
obj* x_198; 
lean::dec(x_193);
lean::dec(x_2);
x_198 = l_Lean_IR_Checker_checkVar___closed__2;
return x_198;
}
else
{
obj* x_200; 
lean::dec(x_193);
x_200 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_200;
}
}
default:
{
obj* x_202; obj* x_205; 
x_202 = lean::cnstr_get(x_1, 0);
lean::inc(x_202);
lean::dec(x_1);
x_205 = l_Lean_IR_Checker_checkObjVar(x_202, x_2);
if (lean::obj_tag(x_205) == 0)
{
obj* x_206; obj* x_208; obj* x_209; 
x_206 = lean::cnstr_get(x_205, 0);
if (lean::is_exclusive(x_205)) {
 x_208 = x_205;
} else {
 lean::inc(x_206);
 lean::dec(x_205);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_206);
return x_209;
}
else
{
uint8 x_211; uint8 x_212; 
lean::dec(x_205);
x_211 = 1;
x_212 = l_Lean_IR_IRType_beq___main(x_0, x_211);
if (x_212 == 0)
{
obj* x_213; 
x_213 = l_Lean_IR_Checker_checkType___closed__1;
return x_213;
}
else
{
obj* x_214; 
x_214 = l_Lean_IR_Checker_checkVar___closed__2;
return x_214;
}
}
}
}
}
}
obj* l_Lean_IR_Checker_checkExpr___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_IR_Checker_checkExpr___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkExpr(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkExpr___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkExpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_IR_Checker_checkExpr(x_3, x_1, x_2);
return x_4;
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
obj* x_2; uint8 x_4; obj* x_5; obj* x_7; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
lean::inc(x_5);
x_12 = l_Lean_IR_Checker_checkExpr___main(x_4, x_5, x_1);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
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
uint8 x_23; 
lean::dec(x_12);
lean::inc(x_1);
x_23 = l_Lean_IR_Context_contains(x_1, x_2);
if (x_23 == 0)
{
obj* x_24; 
x_24 = l_Lean_IR_Context_addLocal(x_1, x_2, x_4, x_5);
x_0 = x_7;
x_1 = x_24;
goto _start;
}
else
{
obj* x_30; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_2);
x_30 = l_Lean_IR_Checker_checkFnBody___main___closed__1;
return x_30;
}
}
}
case 1:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_42; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
lean::dec(x_0);
x_40 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_42 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_33, x_33, x_40, x_1, x_1);
if (lean::obj_tag(x_42) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_33);
lean::dec(x_37);
lean::dec(x_31);
lean::dec(x_35);
x_48 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_50 = x_42;
} else {
 lean::inc(x_48);
 lean::dec(x_42);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
return x_51;
}
else
{
obj* x_52; obj* x_56; 
x_52 = lean::cnstr_get(x_42, 0);
lean::inc(x_52);
lean::dec(x_42);
lean::inc(x_35);
x_56 = l_Lean_IR_Checker_checkFnBody___main(x_35, x_52);
if (lean::obj_tag(x_56) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_1);
lean::dec(x_33);
lean::dec(x_37);
lean::dec(x_31);
lean::dec(x_35);
x_62 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_64 = x_56;
} else {
 lean::inc(x_62);
 lean::dec(x_56);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
return x_65;
}
else
{
uint8 x_68; 
lean::dec(x_56);
lean::inc(x_1);
x_68 = l_Lean_IR_Context_contains(x_1, x_31);
if (x_68 == 0)
{
obj* x_69; 
x_69 = l_Lean_IR_Context_addJP(x_1, x_31, x_33, x_35);
x_0 = x_37;
x_1 = x_69;
goto _start;
}
else
{
obj* x_76; 
lean::dec(x_1);
lean::dec(x_33);
lean::dec(x_37);
lean::dec(x_31);
lean::dec(x_35);
x_76 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_76;
}
}
}
}
case 4:
{
obj* x_77; obj* x_79; obj* x_81; obj* x_85; 
x_77 = lean::cnstr_get(x_0, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_0, 3);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_0, 4);
lean::inc(x_81);
lean::dec(x_0);
lean::inc(x_1);
x_85 = l_Lean_IR_Checker_checkVar(x_77, x_1);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; obj* x_91; obj* x_92; 
lean::dec(x_81);
lean::dec(x_79);
lean::dec(x_1);
x_89 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_91 = x_85;
} else {
 lean::inc(x_89);
 lean::dec(x_85);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_95; 
lean::dec(x_85);
lean::inc(x_1);
x_95 = l_Lean_IR_Checker_checkVar(x_79, x_1);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_81);
lean::dec(x_1);
x_98 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
lean::dec(x_95);
x_0 = x_81;
goto _start;
}
}
}
case 5:
{
obj* x_104; obj* x_106; obj* x_110; 
x_104 = lean::cnstr_get(x_0, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_0, 2);
lean::inc(x_106);
lean::dec(x_0);
lean::inc(x_1);
x_110 = l_Lean_IR_Checker_checkVar(x_104, x_1);
if (lean::obj_tag(x_110) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_106);
lean::dec(x_1);
x_113 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_115 = x_110;
} else {
 lean::inc(x_113);
 lean::dec(x_110);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
return x_116;
}
else
{
lean::dec(x_110);
x_0 = x_106;
goto _start;
}
}
case 6:
{
obj* x_119; obj* x_121; obj* x_125; 
x_119 = lean::cnstr_get(x_0, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_0, 2);
lean::inc(x_121);
lean::dec(x_0);
lean::inc(x_1);
x_125 = l_Lean_IR_Checker_checkVar(x_119, x_1);
if (lean::obj_tag(x_125) == 0)
{
obj* x_128; obj* x_130; obj* x_131; 
lean::dec(x_1);
lean::dec(x_121);
x_128 = lean::cnstr_get(x_125, 0);
if (lean::is_exclusive(x_125)) {
 x_130 = x_125;
} else {
 lean::inc(x_128);
 lean::dec(x_125);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_128);
return x_131;
}
else
{
lean::dec(x_125);
x_0 = x_121;
goto _start;
}
}
case 7:
{
obj* x_134; obj* x_136; obj* x_140; 
x_134 = lean::cnstr_get(x_0, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_0, 2);
lean::inc(x_136);
lean::dec(x_0);
lean::inc(x_1);
x_140 = l_Lean_IR_Checker_checkVar(x_134, x_1);
if (lean::obj_tag(x_140) == 0)
{
obj* x_143; obj* x_145; obj* x_146; 
lean::dec(x_1);
lean::dec(x_136);
x_143 = lean::cnstr_get(x_140, 0);
if (lean::is_exclusive(x_140)) {
 x_145 = x_140;
} else {
 lean::inc(x_143);
 lean::dec(x_140);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_143);
return x_146;
}
else
{
lean::dec(x_140);
x_0 = x_136;
goto _start;
}
}
case 8:
{
obj* x_149; 
x_149 = lean::cnstr_get(x_0, 1);
lean::inc(x_149);
lean::dec(x_0);
x_0 = x_149;
goto _start;
}
case 9:
{
obj* x_153; obj* x_155; obj* x_159; 
x_153 = lean::cnstr_get(x_0, 1);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_0, 2);
lean::inc(x_155);
lean::dec(x_0);
lean::inc(x_1);
x_159 = l_Lean_IR_Checker_checkVar(x_153, x_1);
if (lean::obj_tag(x_159) == 0)
{
obj* x_162; obj* x_164; obj* x_165; 
lean::dec(x_1);
lean::dec(x_155);
x_162 = lean::cnstr_get(x_159, 0);
if (lean::is_exclusive(x_159)) {
 x_164 = x_159;
} else {
 lean::inc(x_162);
 lean::dec(x_159);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
return x_165;
}
else
{
obj* x_167; obj* x_168; 
lean::dec(x_159);
x_167 = lean::mk_nat_obj(0ul);
x_168 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_155, x_167, x_1);
lean::dec(x_155);
return x_168;
}
}
case 10:
{
obj* x_170; obj* x_173; 
x_170 = lean::cnstr_get(x_0, 0);
lean::inc(x_170);
lean::dec(x_0);
x_173 = l_Lean_IR_Checker_checkArg(x_170, x_1);
return x_173;
}
case 11:
{
obj* x_174; obj* x_176; obj* x_180; 
x_174 = lean::cnstr_get(x_0, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_0, 1);
lean::inc(x_176);
lean::dec(x_0);
lean::inc(x_1);
x_180 = l_Lean_IR_Checker_checkJP(x_174, x_1);
if (lean::obj_tag(x_180) == 0)
{
obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_1);
lean::dec(x_176);
x_183 = lean::cnstr_get(x_180, 0);
if (lean::is_exclusive(x_180)) {
 x_185 = x_180;
} else {
 lean::inc(x_183);
 lean::dec(x_180);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_183);
return x_186;
}
else
{
obj* x_188; obj* x_189; 
lean::dec(x_180);
x_188 = lean::mk_nat_obj(0ul);
x_189 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_176, x_188, x_1);
lean::dec(x_176);
return x_189;
}
}
case 12:
{
obj* x_192; 
lean::dec(x_1);
x_192 = l_Lean_IR_Checker_checkVar___closed__2;
return x_192;
}
default:
{
obj* x_193; obj* x_195; obj* x_197; obj* x_201; 
x_193 = lean::cnstr_get(x_0, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_0, 2);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_0, 3);
lean::inc(x_197);
lean::dec(x_0);
lean::inc(x_1);
x_201 = l_Lean_IR_Checker_checkVar(x_193, x_1);
if (lean::obj_tag(x_201) == 0)
{
obj* x_205; obj* x_207; obj* x_208; 
lean::dec(x_1);
lean::dec(x_197);
lean::dec(x_195);
x_205 = lean::cnstr_get(x_201, 0);
if (lean::is_exclusive(x_201)) {
 x_207 = x_201;
} else {
 lean::inc(x_205);
 lean::dec(x_201);
 x_207 = lean::box(0);
}
if (lean::is_scalar(x_207)) {
 x_208 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_208 = x_207;
}
lean::cnstr_set(x_208, 0, x_205);
return x_208;
}
else
{
obj* x_211; 
lean::dec(x_201);
lean::inc(x_1);
x_211 = l_Lean_IR_Checker_checkVar(x_195, x_1);
if (lean::obj_tag(x_211) == 0)
{
obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_1);
lean::dec(x_197);
x_214 = lean::cnstr_get(x_211, 0);
if (lean::is_exclusive(x_211)) {
 x_216 = x_211;
} else {
 lean::inc(x_214);
 lean::dec(x_211);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
return x_217;
}
else
{
lean::dec(x_211);
x_0 = x_197;
goto _start;
}
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
obj* x_0; 
x_0 = lean::mk_string("IR check failed at '");
return x_0;
}
}
obj* _init_l_Lean_IR_Decl_check___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', error: ");
return x_0;
}
}
obj* l_Lean_IR_Decl_check(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::box(0);
lean::inc(x_0);
x_4 = l_Lean_IR_Checker_checkDecl___main(x_0, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
} else {
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = l_Lean_IR_Decl_id___main(x_0);
lean::dec(x_0);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_11);
x_15 = l_Lean_IR_Decl_check___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = l_Lean_IR_Decl_check___closed__2;
x_19 = lean::string_append(x_16, x_18);
x_20 = lean::string_append(x_19, x_5);
lean::dec(x_5);
if (lean::is_scalar(x_10)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_10;
 lean::cnstr_set_tag(x_10, 1);
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_8);
return x_22;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_4);
lean::dec(x_0);
x_25 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_27 = x_1;
} else {
 lean::inc(x_25);
 lean::dec(x_1);
 x_27 = lean::box(0);
}
x_28 = lean::box(0);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_25);
return x_29;
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
 l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
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
