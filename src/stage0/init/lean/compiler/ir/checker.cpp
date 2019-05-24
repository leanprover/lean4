// Lean compiler output
// Module: init.lean.compiler.ir.checker
// Imports: init.lean.compiler.ir.compilerm
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
obj* l_Lean_IR_Checker_getDecl(obj*, obj*);
extern obj* l_Lean_IR_getDecl___closed__1;
obj* l_Lean_IR_Checker_checkType(uint8, obj*, obj*);
obj* l_Lean_IR_Checker_checkExpr___main(uint8, obj*, obj*);
obj* l_Lean_IR_Checker_checkFullApp___closed__1;
obj* l_Lean_IR_Checker_getDecl___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_Checker_checkPartialApp___closed__1;
obj* l_Lean_IR_Checker_checkPartialApp___closed__2;
obj* l_Lean_IR_LocalContext_addLocal(obj*, obj*, uint8, obj*);
uint8 l_Lean_IR_LocalContext_isParam(obj*, obj*);
uint8 l_Lean_IR_LocalContext_contains(obj*, obj*);
obj* l_Lean_IR_Checker_checkScalarVar(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
obj* l_Lean_IR_Checker_checkFullApp___boxed(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main___closed__1;
obj* l_Lean_IR_Checker_checkExpr___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkDecl(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main___closed__2;
obj* l_Lean_IR_Checker_checkFullApp___closed__4;
obj* l_Lean_IR_checkDecls(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_isObj___main(uint8);
obj* l_Lean_IR_Checker_checkType___closed__1;
obj* l_Lean_IR_Checker_checkDecl___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_checkDecl(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkType___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_checkDecl___closed__2;
obj* l_Lean_IR_Checker_checkFnBody(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_Checker_withParams(obj*, obj*, obj*);
obj* l_Lean_IR_findEnvDecl_x_27(obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_addJP(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkPartialApp___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkJP(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_IR_Checker_checkFullApp(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_name___main(obj*);
obj* l_Lean_IR_LocalContext_addParam(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Lean_IR_CtorInfo_isRef(obj*);
obj* l_Lean_IR_LocalContext_getType(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkPartialApp___closed__3;
obj* l_Lean_IR_Checker_checkObjType___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkVar___closed__2;
obj* l_Lean_IR_Checker_checkScalarType(uint8, obj*);
obj* l_Lean_IR_Checker_checkArg(obj*, obj*);
obj* l_Lean_IR_Checker_checkFullApp___closed__3;
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_Checker_checkExpr___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkArgs___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkPartialApp(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkVar(obj*, obj*);
obj* l_Lean_IR_checkDecl___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkVarType(obj*, obj*, obj*);
obj* l_Lean_IR_getEnv___rarg(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_LocalContext_isLocalVar(obj*, obj*);
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
obj* l_Lean_IR_Decl_params___main(obj*);
obj* l_Lean_IR_Checker_checkVar___closed__1;
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFullApp___closed__2;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_Checker_checkArgs(obj*, obj*);
obj* l_Lean_IR_checkDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_withParams___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkObjType(uint8, obj*);
obj* l_Lean_IR_checkDecls___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkScalarType___boxed(obj*, obj*);
uint8 l_Lean_IR_LocalContext_isJP(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFnBody___main(obj*, obj*);
obj* l_Lean_IR_Checker_checkObjVar(obj*, obj*);
obj* l_Lean_IR_Checker_checkJP___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_isScalar___main(uint8);
obj* l_Lean_IR_Checker_checkExpr(uint8, obj*, obj*);
obj* l_Lean_IR_Checker_getDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 2);
x_4 = l_Lean_IR_findEnvDecl_x_27(x_2, x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_0);
x_7 = l_Lean_IR_getDecl___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
}
}
obj* l_Lean_IR_Checker_getDecl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Checker_getDecl(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
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
obj* x_2; uint8 x_6; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
lean::inc(x_2);
x_6 = l_Lean_IR_LocalContext_isLocalVar(x_2, x_0);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = l_Lean_IR_LocalContext_isParam(x_2, x_0);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_8 = l_Nat_repr(x_0);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_Lean_IR_Checker_checkVar___closed__1;
x_13 = lean::string_append(x_12, x_10);
lean::dec(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_13, x_15);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l_Lean_IR_Checker_checkVar___closed__2;
return x_19;
}
}
else
{
obj* x_22; 
lean::dec(x_0);
lean::dec(x_2);
x_22 = l_Lean_IR_Checker_checkVar___closed__2;
return x_22;
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
obj* x_2; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_LocalContext_isJP(x_2, x_0);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_6 = l_Nat_repr(x_0);
x_7 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = l_Lean_IR_Checker_checkJP___closed__1;
x_11 = lean::string_append(x_10, x_8);
lean::dec(x_8);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
return x_17;
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
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = l_Lean_IR_LocalContext_getType(x_3, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_8 = l_Nat_repr(x_0);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_Lean_IR_Checker_checkVar___closed__1;
x_13 = lean::string_append(x_12, x_10);
lean::dec(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_13, x_15);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
obj* x_19; obj* x_22; uint8 x_23; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_6, 0);
lean::inc(x_19);
lean::dec(x_6);
x_22 = lean::apply_1(x_1, x_19);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_24; 
x_24 = l_Lean_IR_Checker_checkType___closed__1;
return x_24;
}
else
{
obj* x_25; 
x_25 = l_Lean_IR_Checker_checkVar___closed__2;
return x_25;
}
}
}
}
obj* l_Lean_IR_Checker_checkObjVar(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_LocalContext_getType(x_2, x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_6 = l_Nat_repr(x_0);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = l_Lean_IR_Checker_checkVar___closed__1;
x_11 = lean::string_append(x_10, x_8);
lean::dec(x_8);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_17; uint8 x_20; uint8 x_21; 
lean::dec(x_0);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
lean::dec(x_5);
x_20 = lean::unbox(x_17);
x_21 = l_Lean_IR_IRType_isObj___main(x_20);
if (x_21 == 0)
{
obj* x_22; 
x_22 = l_Lean_IR_Checker_checkType___closed__1;
return x_22;
}
else
{
obj* x_23; 
x_23 = l_Lean_IR_Checker_checkVar___closed__2;
return x_23;
}
}
}
}
obj* l_Lean_IR_Checker_checkScalarVar(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_LocalContext_getType(x_2, x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_6 = l_Nat_repr(x_0);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = l_Lean_IR_Checker_checkVar___closed__1;
x_11 = lean::string_append(x_10, x_8);
lean::dec(x_8);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_17; uint8 x_20; uint8 x_21; 
lean::dec(x_0);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
lean::dec(x_5);
x_20 = lean::unbox(x_17);
x_21 = l_Lean_IR_IRType_isScalar___main(x_20);
if (x_21 == 0)
{
obj* x_22; 
x_22 = l_Lean_IR_Checker_checkType___closed__1;
return x_22;
}
else
{
obj* x_23; 
x_23 = l_Lean_IR_Checker_checkVar___closed__2;
return x_23;
}
}
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("incorrect number of arguments to '");
return x_0;
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', ");
return x_0;
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" provided, ");
return x_0;
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" expected");
return x_0;
}
}
obj* l_Lean_IR_Checker_checkFullApp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_0);
x_4 = l_Lean_IR_Checker_getDecl(x_0, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; uint8 x_19; 
x_11 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_13 = x_4;
} else {
 lean::inc(x_11);
 lean::dec(x_4);
 x_13 = lean::box(0);
}
x_14 = lean::array_get_size(x_1);
x_15 = l_Lean_IR_Decl_params___main(x_11);
lean::dec(x_11);
x_17 = lean::array_get_size(x_15);
lean::dec(x_15);
x_19 = lean::nat_dec_eq(x_14, x_17);
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_2);
x_21 = l_Lean_Name_toString___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_0);
x_23 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_27 = lean::string_append(x_24, x_26);
x_28 = l_Nat_repr(x_14);
x_29 = lean::string_append(x_27, x_28);
lean::dec(x_28);
x_31 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_32 = lean::string_append(x_29, x_31);
x_33 = l_Nat_repr(x_17);
x_34 = lean::string_append(x_32, x_33);
lean::dec(x_33);
x_36 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_37 = lean::string_append(x_34, x_36);
if (lean::is_scalar(x_13)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_13;
 lean::cnstr_set_tag(x_13, 0);
}
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
else
{
obj* x_43; obj* x_44; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_14);
lean::dec(x_17);
x_43 = lean::mk_nat_obj(0ul);
x_44 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_43, x_2);
return x_44;
}
}
}
}
obj* l_Lean_IR_Checker_checkFullApp___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkFullApp(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("too many arguments too partial application '");
return x_0;
}
}
obj* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', num. args: ");
return x_0;
}
}
obj* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", arity: ");
return x_0;
}
}
obj* l_Lean_IR_Checker_checkPartialApp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_0);
x_4 = l_Lean_IR_Checker_getDecl(x_0, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; uint8 x_19; 
x_11 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_13 = x_4;
} else {
 lean::inc(x_11);
 lean::dec(x_4);
 x_13 = lean::box(0);
}
x_14 = lean::array_get_size(x_1);
x_15 = l_Lean_IR_Decl_params___main(x_11);
lean::dec(x_11);
x_17 = lean::array_get_size(x_15);
lean::dec(x_15);
x_19 = lean::nat_dec_lt(x_14, x_17);
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; 
lean::dec(x_2);
x_21 = l_Lean_Name_toString___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_0);
x_23 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_27 = lean::string_append(x_24, x_26);
x_28 = l_Nat_repr(x_14);
x_29 = lean::string_append(x_27, x_28);
lean::dec(x_28);
x_31 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_32 = lean::string_append(x_29, x_31);
x_33 = l_Nat_repr(x_17);
x_34 = lean::string_append(x_32, x_33);
lean::dec(x_33);
if (lean::is_scalar(x_13)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_13;
 lean::cnstr_set_tag(x_13, 0);
}
lean::cnstr_set(x_36, 0, x_34);
return x_36;
}
else
{
obj* x_41; obj* x_42; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_14);
lean::dec(x_17);
x_41 = lean::mk_nat_obj(0ul);
x_42 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_41, x_2);
return x_42;
}
}
}
}
obj* l_Lean_IR_Checker_checkPartialApp___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkPartialApp(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
x_8 = l_Lean_IR_CtorInfo_isRef(x_3);
lean::dec(x_3);
if (x_8 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::mk_nat_obj(0ul);
x_11 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_10, x_2);
lean::dec(x_5);
return x_11;
}
else
{
obj* x_13; 
x_13 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_5);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_18 = x_13;
} else {
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_13);
x_21 = lean::mk_nat_obj(0ul);
x_22 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_21, x_2);
lean::dec(x_5);
return x_22;
}
}
}
case 2:
{
obj* x_24; obj* x_26; obj* x_30; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_1, 2);
lean::inc(x_26);
lean::dec(x_1);
lean::inc(x_2);
x_30 = l_Lean_IR_Checker_checkObjVar(x_24, x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_2);
lean::dec(x_26);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_38; obj* x_40; 
lean::dec(x_30);
x_38 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_40 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_26, x_38, x_2);
lean::dec(x_26);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_2);
x_43 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_45 = x_40;
} else {
 lean::inc(x_43);
 lean::dec(x_40);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_48; 
lean::dec(x_40);
x_48 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_48;
}
}
}
case 4:
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_1, 1);
lean::inc(x_50);
lean::dec(x_1);
x_53 = l_Lean_IR_Checker_checkObjVar(x_50, x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_56 = x_53;
} else {
 lean::inc(x_54);
 lean::dec(x_53);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
return x_57;
}
else
{
uint8 x_59; uint8 x_60; 
lean::dec(x_53);
x_59 = 5;
x_60 = l_Lean_IR_IRType_beq___main(x_0, x_59);
if (x_60 == 0)
{
obj* x_61; 
x_61 = l_Lean_IR_Checker_checkType___closed__1;
return x_61;
}
else
{
obj* x_62; 
x_62 = l_Lean_IR_Checker_checkVar___closed__2;
return x_62;
}
}
}
case 5:
{
obj* x_63; obj* x_67; 
x_63 = lean::cnstr_get(x_1, 2);
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
x_74 = l_Lean_IR_Checker_checkScalarType(x_0, x_2);
lean::dec(x_2);
return x_74;
}
}
case 6:
{
obj* x_76; obj* x_78; obj* x_81; 
x_76 = lean::cnstr_get(x_1, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_1, 1);
lean::inc(x_78);
lean::dec(x_1);
x_81 = l_Lean_IR_Checker_checkFullApp(x_76, x_78, x_2);
lean::dec(x_78);
return x_81;
}
case 7:
{
obj* x_83; obj* x_85; obj* x_89; 
x_83 = lean::cnstr_get(x_1, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_1, 1);
lean::inc(x_85);
lean::dec(x_1);
lean::inc(x_2);
x_89 = l_Lean_IR_Checker_checkPartialApp(x_83, x_85, x_2);
lean::dec(x_85);
if (lean::obj_tag(x_89) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_2);
x_92 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_92);
 lean::dec(x_89);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
return x_95;
}
else
{
obj* x_97; 
lean::dec(x_89);
x_97 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_97;
}
}
case 8:
{
obj* x_99; obj* x_101; obj* x_105; 
x_99 = lean::cnstr_get(x_1, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_1, 1);
lean::inc(x_101);
lean::dec(x_1);
lean::inc(x_2);
x_105 = l_Lean_IR_Checker_checkObjVar(x_99, x_2);
if (lean::obj_tag(x_105) == 0)
{
obj* x_108; obj* x_110; obj* x_111; 
lean::dec(x_101);
lean::dec(x_2);
x_108 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_110 = x_105;
} else {
 lean::inc(x_108);
 lean::dec(x_105);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
return x_111;
}
else
{
obj* x_113; obj* x_114; 
lean::dec(x_105);
x_113 = lean::mk_nat_obj(0ul);
x_114 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_101, x_113, x_2);
lean::dec(x_101);
return x_114;
}
}
case 9:
{
uint8 x_116; obj* x_117; obj* x_120; 
x_116 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_117 = lean::cnstr_get(x_1, 0);
lean::inc(x_117);
lean::dec(x_1);
x_120 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
if (lean::obj_tag(x_120) == 0)
{
obj* x_123; obj* x_125; obj* x_126; 
lean::dec(x_117);
lean::dec(x_2);
x_123 = lean::cnstr_get(x_120, 0);
if (lean::is_exclusive(x_120)) {
 x_125 = x_120;
} else {
 lean::inc(x_123);
 lean::dec(x_120);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
return x_126;
}
else
{
obj* x_130; 
lean::dec(x_120);
lean::inc(x_2);
lean::inc(x_117);
x_130 = l_Lean_IR_Checker_checkScalarVar(x_117, x_2);
if (lean::obj_tag(x_130) == 0)
{
obj* x_133; obj* x_135; obj* x_136; 
lean::dec(x_117);
lean::dec(x_2);
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
obj* x_137; obj* x_138; obj* x_141; 
if (lean::is_exclusive(x_130)) {
 lean::cnstr_release(x_130, 0);
 x_137 = x_130;
} else {
 lean::dec(x_130);
 x_137 = lean::box(0);
}
x_138 = lean::cnstr_get(x_2, 1);
lean::inc(x_138);
lean::dec(x_2);
x_141 = l_Lean_IR_LocalContext_getType(x_138, x_117);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_143; obj* x_144; obj* x_146; obj* x_147; obj* x_149; obj* x_150; obj* x_151; 
x_142 = l_Nat_repr(x_117);
x_143 = l_Lean_IR_VarId_HasToString___closed__1;
x_144 = lean::string_append(x_143, x_142);
lean::dec(x_142);
x_146 = l_Lean_IR_Checker_checkVar___closed__1;
x_147 = lean::string_append(x_146, x_144);
lean::dec(x_144);
x_149 = l_Char_HasRepr___closed__1;
x_150 = lean::string_append(x_147, x_149);
if (lean::is_scalar(x_137)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_137;
 lean::cnstr_set_tag(x_137, 0);
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
else
{
obj* x_154; uint8 x_157; uint8 x_158; 
lean::dec(x_117);
lean::dec(x_137);
x_154 = lean::cnstr_get(x_141, 0);
lean::inc(x_154);
lean::dec(x_141);
x_157 = lean::unbox(x_154);
x_158 = l_Lean_IR_IRType_beq___main(x_157, x_116);
if (x_158 == 0)
{
obj* x_159; 
x_159 = l_Lean_IR_Checker_checkType___closed__1;
return x_159;
}
else
{
obj* x_160; 
x_160 = l_Lean_IR_Checker_checkVar___closed__2;
return x_160;
}
}
}
}
}
case 10:
{
obj* x_161; obj* x_164; 
x_161 = lean::cnstr_get(x_1, 0);
lean::inc(x_161);
lean::dec(x_1);
x_164 = l_Lean_IR_Checker_checkScalarType(x_0, x_2);
if (lean::obj_tag(x_164) == 0)
{
obj* x_167; obj* x_169; obj* x_170; 
lean::dec(x_161);
lean::dec(x_2);
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
obj* x_172; 
lean::dec(x_164);
x_172 = l_Lean_IR_Checker_checkObjVar(x_161, x_2);
return x_172;
}
}
case 11:
{
obj* x_173; 
x_173 = lean::cnstr_get(x_1, 0);
lean::inc(x_173);
lean::dec(x_1);
if (lean::obj_tag(x_173) == 0)
{
obj* x_178; 
lean::dec(x_173);
lean::dec(x_2);
x_178 = l_Lean_IR_Checker_checkVar___closed__2;
return x_178;
}
else
{
obj* x_180; 
lean::dec(x_173);
x_180 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_180;
}
}
case 12:
{
obj* x_182; obj* x_185; 
x_182 = lean::cnstr_get(x_1, 0);
lean::inc(x_182);
lean::dec(x_1);
x_185 = l_Lean_IR_Checker_checkObjVar(x_182, x_2);
if (lean::obj_tag(x_185) == 0)
{
obj* x_186; obj* x_188; obj* x_189; 
x_186 = lean::cnstr_get(x_185, 0);
if (lean::is_exclusive(x_185)) {
 x_188 = x_185;
} else {
 lean::inc(x_186);
 lean::dec(x_185);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_186);
return x_189;
}
else
{
uint8 x_191; uint8 x_192; 
lean::dec(x_185);
x_191 = 1;
x_192 = l_Lean_IR_IRType_beq___main(x_0, x_191);
if (x_192 == 0)
{
obj* x_193; 
x_193 = l_Lean_IR_Checker_checkType___closed__1;
return x_193;
}
else
{
obj* x_194; 
x_194 = l_Lean_IR_Checker_checkVar___closed__2;
return x_194;
}
}
}
case 13:
{
obj* x_195; obj* x_198; 
x_195 = lean::cnstr_get(x_1, 0);
lean::inc(x_195);
lean::dec(x_1);
x_198 = l_Lean_IR_Checker_checkObjVar(x_195, x_2);
if (lean::obj_tag(x_198) == 0)
{
obj* x_199; obj* x_201; obj* x_202; 
x_199 = lean::cnstr_get(x_198, 0);
if (lean::is_exclusive(x_198)) {
 x_201 = x_198;
} else {
 lean::inc(x_199);
 lean::dec(x_198);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
return x_202;
}
else
{
uint8 x_204; uint8 x_205; 
lean::dec(x_198);
x_204 = 1;
x_205 = l_Lean_IR_IRType_beq___main(x_0, x_204);
if (x_205 == 0)
{
obj* x_206; 
x_206 = l_Lean_IR_Checker_checkType___closed__1;
return x_206;
}
else
{
obj* x_207; 
x_207 = l_Lean_IR_Checker_checkVar___closed__2;
return x_207;
}
}
}
default:
{
obj* x_208; obj* x_212; 
x_208 = lean::cnstr_get(x_1, 1);
lean::inc(x_208);
lean::dec(x_1);
lean::inc(x_2);
x_212 = l_Lean_IR_Checker_checkObjVar(x_208, x_2);
if (lean::obj_tag(x_212) == 0)
{
obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_2);
x_214 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_216 = x_212;
} else {
 lean::inc(x_214);
 lean::dec(x_212);
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
obj* x_219; 
lean::dec(x_212);
x_219 = l_Lean_IR_Checker_checkObjType(x_0, x_2);
lean::dec(x_2);
return x_219;
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
x_17 = l_Lean_IR_LocalContext_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_LocalContext_addParam(x_3, x_10);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_0, x_0, x_9, x_5, x_2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_11 = x_2;
} else {
 lean::dec(x_2);
 x_11 = lean::box(0);
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_10, 0);
lean::inc(x_20);
lean::dec(x_10);
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_3);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_7);
x_24 = lean::apply_1(x_1, x_23);
return x_24;
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
x_17 = l_Lean_IR_LocalContext_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_LocalContext_addParam(x_3, x_10);
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
obj* x_22; obj* x_24; obj* x_26; obj* x_28; uint8 x_30; 
lean::dec(x_12);
x_22 = lean::cnstr_get(x_1, 0);
x_24 = lean::cnstr_get(x_1, 1);
x_26 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_28 = x_1;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_1);
 x_28 = lean::box(0);
}
lean::inc(x_24);
x_30 = l_Lean_IR_LocalContext_contains(x_24, x_2);
if (x_30 == 0)
{
obj* x_31; obj* x_32; 
x_31 = l_Lean_IR_LocalContext_addLocal(x_24, x_2, x_4, x_5);
if (lean::is_scalar(x_28)) {
 x_32 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_32 = x_28;
}
lean::cnstr_set(x_32, 0, x_22);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set(x_32, 2, x_26);
x_0 = x_7;
x_1 = x_32;
goto _start;
}
else
{
obj* x_41; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_22);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_24);
lean::dec(x_26);
x_41 = l_Lean_IR_Checker_checkFnBody___main___closed__1;
return x_41;
}
}
}
case 1:
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_60; 
x_42 = lean::cnstr_get(x_0, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_0, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_0, 2);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_0, 3);
lean::inc(x_48);
lean::dec(x_0);
x_51 = lean::cnstr_get(x_1, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_1, 1);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_1, 2);
lean::inc(x_55);
x_57 = lean::mk_nat_obj(0ul);
lean::inc(x_53);
x_59 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_44, x_44, x_57, x_53, x_1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_60 = x_1;
} else {
 lean::dec(x_1);
 x_60 = lean::box(0);
}
if (lean::obj_tag(x_59) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_51);
lean::dec(x_53);
lean::dec(x_55);
lean::dec(x_48);
lean::dec(x_60);
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_69 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_71 = x_59;
} else {
 lean::inc(x_69);
 lean::dec(x_59);
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
obj* x_73; obj* x_78; obj* x_80; 
x_73 = lean::cnstr_get(x_59, 0);
lean::inc(x_73);
lean::dec(x_59);
lean::inc(x_55);
lean::inc(x_51);
if (lean::is_scalar(x_60)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_60;
}
lean::cnstr_set(x_78, 0, x_51);
lean::cnstr_set(x_78, 1, x_73);
lean::cnstr_set(x_78, 2, x_55);
lean::inc(x_46);
x_80 = l_Lean_IR_Checker_checkFnBody___main(x_46, x_78);
if (lean::obj_tag(x_80) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_51);
lean::dec(x_53);
lean::dec(x_55);
lean::dec(x_48);
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_88 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_90 = x_80;
} else {
 lean::inc(x_88);
 lean::dec(x_80);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
return x_91;
}
else
{
uint8 x_94; 
lean::dec(x_80);
lean::inc(x_53);
x_94 = l_Lean_IR_LocalContext_contains(x_53, x_42);
if (x_94 == 0)
{
obj* x_95; obj* x_96; 
x_95 = l_Lean_IR_LocalContext_addJP(x_53, x_42, x_44, x_46);
x_96 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_96, 0, x_51);
lean::cnstr_set(x_96, 1, x_95);
lean::cnstr_set(x_96, 2, x_55);
x_0 = x_48;
x_1 = x_96;
goto _start;
}
else
{
obj* x_105; 
lean::dec(x_51);
lean::dec(x_53);
lean::dec(x_55);
lean::dec(x_48);
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_105 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_105;
}
}
}
}
case 2:
{
obj* x_106; obj* x_108; obj* x_110; obj* x_114; 
x_106 = lean::cnstr_get(x_0, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_0, 2);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_0, 3);
lean::inc(x_110);
lean::dec(x_0);
lean::inc(x_1);
x_114 = l_Lean_IR_Checker_checkVar(x_106, x_1);
if (lean::obj_tag(x_114) == 0)
{
obj* x_118; obj* x_120; obj* x_121; 
lean::dec(x_1);
lean::dec(x_108);
lean::dec(x_110);
x_118 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_120 = x_114;
} else {
 lean::inc(x_118);
 lean::dec(x_114);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
return x_121;
}
else
{
obj* x_124; 
lean::dec(x_114);
lean::inc(x_1);
x_124 = l_Lean_IR_Checker_checkArg(x_108, x_1);
if (lean::obj_tag(x_124) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_1);
lean::dec(x_110);
x_127 = lean::cnstr_get(x_124, 0);
if (lean::is_exclusive(x_124)) {
 x_129 = x_124;
} else {
 lean::inc(x_127);
 lean::dec(x_124);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
lean::dec(x_124);
x_0 = x_110;
goto _start;
}
}
}
case 4:
{
obj* x_133; obj* x_135; obj* x_137; obj* x_141; 
x_133 = lean::cnstr_get(x_0, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_0, 2);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_0, 3);
lean::inc(x_137);
lean::dec(x_0);
lean::inc(x_1);
x_141 = l_Lean_IR_Checker_checkVar(x_133, x_1);
if (lean::obj_tag(x_141) == 0)
{
obj* x_145; obj* x_147; obj* x_148; 
lean::dec(x_135);
lean::dec(x_137);
lean::dec(x_1);
x_145 = lean::cnstr_get(x_141, 0);
if (lean::is_exclusive(x_141)) {
 x_147 = x_141;
} else {
 lean::inc(x_145);
 lean::dec(x_141);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_145);
return x_148;
}
else
{
obj* x_151; 
lean::dec(x_141);
lean::inc(x_1);
x_151 = l_Lean_IR_Checker_checkVar(x_135, x_1);
if (lean::obj_tag(x_151) == 0)
{
obj* x_154; obj* x_156; obj* x_157; 
lean::dec(x_137);
lean::dec(x_1);
x_154 = lean::cnstr_get(x_151, 0);
if (lean::is_exclusive(x_151)) {
 x_156 = x_151;
} else {
 lean::inc(x_154);
 lean::dec(x_151);
 x_156 = lean::box(0);
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_154);
return x_157;
}
else
{
lean::dec(x_151);
x_0 = x_137;
goto _start;
}
}
}
case 5:
{
obj* x_160; obj* x_162; obj* x_164; obj* x_168; 
x_160 = lean::cnstr_get(x_0, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_0, 3);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_0, 4);
lean::inc(x_164);
lean::dec(x_0);
lean::inc(x_1);
x_168 = l_Lean_IR_Checker_checkVar(x_160, x_1);
if (lean::obj_tag(x_168) == 0)
{
obj* x_172; obj* x_174; obj* x_175; 
lean::dec(x_162);
lean::dec(x_164);
lean::dec(x_1);
x_172 = lean::cnstr_get(x_168, 0);
if (lean::is_exclusive(x_168)) {
 x_174 = x_168;
} else {
 lean::inc(x_172);
 lean::dec(x_168);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
return x_175;
}
else
{
obj* x_178; 
lean::dec(x_168);
lean::inc(x_1);
x_178 = l_Lean_IR_Checker_checkVar(x_162, x_1);
if (lean::obj_tag(x_178) == 0)
{
obj* x_181; obj* x_183; obj* x_184; 
lean::dec(x_164);
lean::dec(x_1);
x_181 = lean::cnstr_get(x_178, 0);
if (lean::is_exclusive(x_178)) {
 x_183 = x_178;
} else {
 lean::inc(x_181);
 lean::dec(x_178);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_181);
return x_184;
}
else
{
lean::dec(x_178);
x_0 = x_164;
goto _start;
}
}
}
case 7:
{
obj* x_187; obj* x_189; obj* x_193; 
x_187 = lean::cnstr_get(x_0, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_0, 2);
lean::inc(x_189);
lean::dec(x_0);
lean::inc(x_1);
x_193 = l_Lean_IR_Checker_checkVar(x_187, x_1);
if (lean::obj_tag(x_193) == 0)
{
obj* x_196; obj* x_198; obj* x_199; 
lean::dec(x_189);
lean::dec(x_1);
x_196 = lean::cnstr_get(x_193, 0);
if (lean::is_exclusive(x_193)) {
 x_198 = x_193;
} else {
 lean::inc(x_196);
 lean::dec(x_193);
 x_198 = lean::box(0);
}
if (lean::is_scalar(x_198)) {
 x_199 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_199 = x_198;
}
lean::cnstr_set(x_199, 0, x_196);
return x_199;
}
else
{
lean::dec(x_193);
x_0 = x_189;
goto _start;
}
}
case 8:
{
obj* x_202; obj* x_204; obj* x_208; 
x_202 = lean::cnstr_get(x_0, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_0, 1);
lean::inc(x_204);
lean::dec(x_0);
lean::inc(x_1);
x_208 = l_Lean_IR_Checker_checkVar(x_202, x_1);
if (lean::obj_tag(x_208) == 0)
{
obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_1);
lean::dec(x_204);
x_211 = lean::cnstr_get(x_208, 0);
if (lean::is_exclusive(x_208)) {
 x_213 = x_208;
} else {
 lean::inc(x_211);
 lean::dec(x_208);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_211);
return x_214;
}
else
{
lean::dec(x_208);
x_0 = x_204;
goto _start;
}
}
case 9:
{
obj* x_217; 
x_217 = lean::cnstr_get(x_0, 1);
lean::inc(x_217);
lean::dec(x_0);
x_0 = x_217;
goto _start;
}
case 10:
{
obj* x_221; obj* x_223; obj* x_227; 
x_221 = lean::cnstr_get(x_0, 1);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_0, 2);
lean::inc(x_223);
lean::dec(x_0);
lean::inc(x_1);
x_227 = l_Lean_IR_Checker_checkVar(x_221, x_1);
if (lean::obj_tag(x_227) == 0)
{
obj* x_230; obj* x_232; obj* x_233; 
lean::dec(x_1);
lean::dec(x_223);
x_230 = lean::cnstr_get(x_227, 0);
if (lean::is_exclusive(x_227)) {
 x_232 = x_227;
} else {
 lean::inc(x_230);
 lean::dec(x_227);
 x_232 = lean::box(0);
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_230);
return x_233;
}
else
{
obj* x_235; obj* x_236; 
lean::dec(x_227);
x_235 = lean::mk_nat_obj(0ul);
x_236 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_223, x_235, x_1);
lean::dec(x_223);
return x_236;
}
}
case 11:
{
obj* x_238; obj* x_241; 
x_238 = lean::cnstr_get(x_0, 0);
lean::inc(x_238);
lean::dec(x_0);
x_241 = l_Lean_IR_Checker_checkArg(x_238, x_1);
return x_241;
}
case 12:
{
obj* x_242; obj* x_244; obj* x_248; 
x_242 = lean::cnstr_get(x_0, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_0, 1);
lean::inc(x_244);
lean::dec(x_0);
lean::inc(x_1);
x_248 = l_Lean_IR_Checker_checkJP(x_242, x_1);
if (lean::obj_tag(x_248) == 0)
{
obj* x_251; obj* x_253; obj* x_254; 
lean::dec(x_1);
lean::dec(x_244);
x_251 = lean::cnstr_get(x_248, 0);
if (lean::is_exclusive(x_248)) {
 x_253 = x_248;
} else {
 lean::inc(x_251);
 lean::dec(x_248);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_251);
return x_254;
}
else
{
obj* x_256; obj* x_257; 
lean::dec(x_248);
x_256 = lean::mk_nat_obj(0ul);
x_257 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_244, x_256, x_1);
lean::dec(x_244);
return x_257;
}
}
case 13:
{
obj* x_260; 
lean::dec(x_1);
x_260 = l_Lean_IR_Checker_checkVar___closed__2;
return x_260;
}
default:
{
obj* x_261; obj* x_263; obj* x_267; 
x_261 = lean::cnstr_get(x_0, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_0, 2);
lean::inc(x_263);
lean::dec(x_0);
lean::inc(x_1);
x_267 = l_Lean_IR_Checker_checkVar(x_261, x_1);
if (lean::obj_tag(x_267) == 0)
{
obj* x_270; obj* x_272; obj* x_273; 
lean::dec(x_1);
lean::dec(x_263);
x_270 = lean::cnstr_get(x_267, 0);
if (lean::is_exclusive(x_267)) {
 x_272 = x_267;
} else {
 lean::inc(x_270);
 lean::dec(x_267);
 x_272 = lean::box(0);
}
if (lean::is_scalar(x_272)) {
 x_273 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_273 = x_272;
}
lean::cnstr_set(x_273, 0, x_270);
return x_273;
}
else
{
lean::dec(x_267);
x_0 = x_263;
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
x_17 = l_Lean_IR_LocalContext_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_LocalContext_addParam(x_3, x_10);
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
x_17 = l_Lean_IR_LocalContext_contains(x_3, x_14);
lean::dec(x_14);
if (x_17 == 0)
{
obj* x_19; 
x_19 = l_Lean_IR_LocalContext_addParam(x_3, x_10);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::mk_nat_obj(0ul);
x_14 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(x_2, x_2, x_13, x_9, x_1);
lean::dec(x_2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_16 = x_1;
} else {
 lean::dec(x_1);
 x_16 = lean::box(0);
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_23 = x_14;
} else {
 lean::inc(x_21);
 lean::dec(x_14);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
lean::dec(x_14);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_7);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_11);
x_29 = l_Lean_IR_Checker_checkFnBody___main(x_4, x_28);
return x_29;
}
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::cnstr_get(x_1, 1);
lean::inc(x_35);
x_37 = lean::mk_nat_obj(0ul);
x_38 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(x_30, x_30, x_37, x_35, x_1);
lean::dec(x_1);
lean::dec(x_30);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_34);
x_42 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_44 = x_38;
} else {
 lean::inc(x_42);
 lean::dec(x_38);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
lean::dec(x_38);
return x_34;
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
obj* _init_l_Lean_IR_checkDecl___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("IR check failed at '");
return x_0;
}
}
obj* _init_l_Lean_IR_checkDecl___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', error: ");
return x_0;
}
}
obj* l_Lean_IR_checkDecl(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_0);
lean::inc(x_1);
x_13 = l_Lean_IR_Checker_checkDecl___main(x_1, x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_17 = l_Lean_IR_Decl_name___main(x_1);
lean::dec(x_1);
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_17);
x_21 = l_Lean_IR_checkDecl___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = l_Lean_IR_checkDecl___closed__2;
x_25 = lean::string_append(x_22, x_24);
x_26 = lean::string_append(x_25, x_14);
lean::dec(x_14);
if (lean::is_scalar(x_9)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_7);
return x_28;
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_13);
lean::dec(x_1);
x_31 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_9;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_7);
return x_32;
}
}
else
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_4, 0);
x_37 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_39 = x_4;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_4);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
}
obj* l_Lean_IR_checkDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_checkDecl(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_0);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_20; 
x_15 = lean::array_fget(x_1, x_2);
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
lean::inc(x_0);
x_20 = l_Lean_IR_checkDecl(x_0, x_15, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_23 = x_20;
} else {
 lean::inc(x_21);
 lean::dec(x_20);
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
x_2 = x_17;
x_4 = x_25;
goto _start;
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_0);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_20, 0);
x_31 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_33 = x_20;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_20);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
}
obj* l_Lean_IR_checkDecls(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_5 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_0, x_0, x_3, x_1, x_2);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_checkDecls___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_checkDecls(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_checker(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
 l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
 l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
 l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
 l_Lean_IR_Checker_checkFullApp___closed__1 = _init_l_Lean_IR_Checker_checkFullApp___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__1);
 l_Lean_IR_Checker_checkFullApp___closed__2 = _init_l_Lean_IR_Checker_checkFullApp___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__2);
 l_Lean_IR_Checker_checkFullApp___closed__3 = _init_l_Lean_IR_Checker_checkFullApp___closed__3();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__3);
 l_Lean_IR_Checker_checkFullApp___closed__4 = _init_l_Lean_IR_Checker_checkFullApp___closed__4();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__4);
 l_Lean_IR_Checker_checkPartialApp___closed__1 = _init_l_Lean_IR_Checker_checkPartialApp___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__1);
 l_Lean_IR_Checker_checkPartialApp___closed__2 = _init_l_Lean_IR_Checker_checkPartialApp___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__2);
 l_Lean_IR_Checker_checkPartialApp___closed__3 = _init_l_Lean_IR_Checker_checkPartialApp___closed__3();
lean::mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__3);
 l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1 = _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1();
lean::mark_persistent(l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1);
 l_Lean_IR_Checker_checkFnBody___main___closed__1 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__1);
 l_Lean_IR_Checker_checkFnBody___main___closed__2 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__2);
 l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean::mark_persistent(l_Lean_IR_checkDecl___closed__1);
 l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean::mark_persistent(l_Lean_IR_checkDecl___closed__2);
return w;
}
