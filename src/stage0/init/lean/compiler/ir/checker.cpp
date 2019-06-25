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
obj* l_Lean_IR_Checker_checkVarType___boxed(obj*, obj*, obj*);
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
obj* l_Lean_IR_checkDecls(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_isObj___main(uint8);
obj* l_Lean_IR_Checker_checkType___closed__1;
obj* l_Lean_IR_Checker_checkArg___boxed(obj*, obj*);
obj* l_Lean_IR_Checker_checkDecl___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_checkDecl(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkType___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_checkDecl___closed__2;
obj* l_Lean_IR_Checker_checkFnBody(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_Checker_withParams(obj*, obj*, obj*);
obj* l_Lean_IR_findEnvDecl_x27(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkObjVar___boxed(obj*, obj*);
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
extern obj* l_Lean_registerTagAttribute___lambda__5___closed__4;
obj* l_Lean_IR_Checker_checkFullApp(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkScalarVar___boxed(obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
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
obj* l_Lean_IR_Checker_checkVar___boxed(obj*, obj*);
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
obj* l_Array_size(obj*, obj*);
obj* l_Lean_IR_Checker_checkVar___closed__1;
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_Checker_checkFullApp___closed__2;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_Checker_checkJP___boxed(obj*, obj*);
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
obj* l_Lean_IR_Checker_getDecl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 2);
x_5 = l_Lean_IR_findEnvDecl_x27(x_3, x_1, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = l_Lean_IR_getDecl___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
obj* l_Lean_IR_Checker_getDecl___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_getDecl(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_Checker_checkVar___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown variable '");
return x_1;
}
}
obj* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Checker_checkVar(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_isLocalVar(x_3, x_1);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_Lean_IR_LocalContext_isParam(x_3, x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_Lean_IR_Checker_checkVar___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_1);
x_14 = l_Lean_IR_Checker_checkVar___closed__2;
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_1);
x_15 = l_Lean_IR_Checker_checkVar___closed__2;
return x_15;
}
}
}
obj* l_Lean_IR_Checker_checkVar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkVar(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_Checker_checkJP___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown join point '");
return x_1;
}
}
obj* l_Lean_IR_Checker_checkJP(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_isJP(x_3, x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Lean_IR_Checker_checkJP___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; 
lean::dec(x_1);
x_13 = l_Lean_IR_Checker_checkVar___closed__2;
return x_13;
}
}
}
obj* l_Lean_IR_Checker_checkJP___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkJP(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkArg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_IR_Checker_checkVar(x_3, x_2);
return x_4;
}
else
{
obj* x_5; 
x_5 = l_Lean_IR_Checker_checkVar___closed__2;
return x_5;
}
}
}
obj* l_Lean_IR_Checker_checkArg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkArg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = l_Lean_IR_Checker_checkVar___closed__2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::array_fget(x_1, x_2);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_2, x_8);
lean::dec(x_2);
x_10 = l_Lean_IR_Checker_checkArg(x_7, x_3);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
lean::dec(x_9);
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean::dec(x_10);
x_2 = x_9;
goto _start;
}
}
}
}
obj* l_Lean_IR_Checker_checkArgs(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkArgs___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkArgs(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("unexpected type");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Checker_checkType(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::box(x_1);
x_5 = lean::apply_1(x_2, x_4);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_Lean_IR_Checker_checkType___closed__1;
return x_7;
}
else
{
obj* x_8; 
x_8 = l_Lean_IR_Checker_checkVar___closed__2;
return x_8;
}
}
}
obj* l_Lean_IR_Checker_checkType___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_IR_Checker_checkType(x_4, x_2, x_3);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_Checker_checkObjType(uint8 x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_IRType_isObj___main(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkType___closed__1;
return x_4;
}
else
{
obj* x_5; 
x_5 = l_Lean_IR_Checker_checkVar___closed__2;
return x_5;
}
}
}
obj* l_Lean_IR_Checker_checkObjType___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_IR_Checker_checkObjType(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkScalarType(uint8 x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_IRType_isScalar___main(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkType___closed__1;
return x_4;
}
else
{
obj* x_5; 
x_5 = l_Lean_IR_Checker_checkVar___closed__2;
return x_5;
}
}
}
obj* l_Lean_IR_Checker_checkScalarType___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_IR_Checker_checkScalarType(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkVarType(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_3, 1);
x_5 = l_Lean_IR_LocalContext_getType(x_4, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_Lean_IR_Checker_checkVar___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_5, 0);
lean::inc(x_14);
lean::dec(x_5);
x_15 = lean::apply_1(x_2, x_14);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; 
x_17 = l_Lean_IR_Checker_checkType___closed__1;
return x_17;
}
else
{
obj* x_18; 
x_18 = l_Lean_IR_Checker_checkVar___closed__2;
return x_18;
}
}
}
}
obj* l_Lean_IR_Checker_checkVarType___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkObjVar(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_getType(x_3, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Lean_IR_Checker_checkVar___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; uint8 x_14; uint8 x_15; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
x_15 = l_Lean_IR_IRType_isObj___main(x_14);
if (x_15 == 0)
{
obj* x_16; 
x_16 = l_Lean_IR_Checker_checkType___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
return x_17;
}
}
}
}
obj* l_Lean_IR_Checker_checkObjVar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkObjVar(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_Checker_checkScalarVar(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_getType(x_3, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Lean_IR_Checker_checkVar___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; uint8 x_14; uint8 x_15; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
x_15 = l_Lean_IR_IRType_isScalar___main(x_14);
if (x_15 == 0)
{
obj* x_16; 
x_16 = l_Lean_IR_Checker_checkType___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
return x_17;
}
}
}
}
obj* l_Lean_IR_Checker_checkScalarVar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("incorrect number of arguments to '");
return x_1;
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" provided, ");
return x_1;
}
}
obj* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" expected");
return x_1;
}
}
obj* l_Lean_IR_Checker_checkFullApp(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_Checker_getDecl(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params___main(x_9);
lean::dec(x_9);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
x_13 = lean::nat_dec_eq(x_10, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_1);
x_16 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_18 = l_Lean_registerTagAttribute___lambda__5___closed__4;
x_19 = lean::string_append(x_17, x_18);
x_20 = l_Nat_repr(x_10);
x_21 = lean::string_append(x_19, x_20);
lean::dec(x_20);
x_22 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_23 = lean::string_append(x_21, x_22);
x_24 = l_Nat_repr(x_12);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
x_26 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_27 = lean::string_append(x_25, x_26);
lean::cnstr_set_tag(x_4, 0);
lean::cnstr_set(x_4, 0, x_27);
return x_4;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_12);
lean::dec(x_10);
lean::free_heap_obj(x_4);
lean::dec(x_1);
x_28 = lean::mk_nat_obj(0u);
x_29 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_28, x_3);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::array_get_size(x_2);
x_32 = l_Lean_IR_Decl_params___main(x_30);
lean::dec(x_30);
x_33 = lean::array_get_size(x_32);
lean::dec(x_32);
x_34 = lean::nat_dec_eq(x_31, x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_35 = l_Lean_Name_toString___closed__1;
x_36 = l_Lean_Name_toStringWithSep___main(x_35, x_1);
x_37 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_38 = lean::string_append(x_37, x_36);
lean::dec(x_36);
x_39 = l_Lean_registerTagAttribute___lambda__5___closed__4;
x_40 = lean::string_append(x_38, x_39);
x_41 = l_Nat_repr(x_31);
x_42 = lean::string_append(x_40, x_41);
lean::dec(x_41);
x_43 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_44 = lean::string_append(x_42, x_43);
x_45 = l_Nat_repr(x_33);
x_46 = lean::string_append(x_44, x_45);
lean::dec(x_45);
x_47 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_48 = lean::string_append(x_46, x_47);
x_49 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_33);
lean::dec(x_31);
lean::dec(x_1);
x_50 = lean::mk_nat_obj(0u);
x_51 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_50, x_3);
return x_51;
}
}
}
}
}
obj* l_Lean_IR_Checker_checkFullApp___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("too many arguments too partial application '");
return x_1;
}
}
obj* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("', num. args: ");
return x_1;
}
}
obj* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", arity: ");
return x_1;
}
}
obj* l_Lean_IR_Checker_checkPartialApp(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_Checker_getDecl(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params___main(x_9);
lean::dec(x_9);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
x_13 = lean::nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_1);
x_16 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_18 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_19 = lean::string_append(x_17, x_18);
x_20 = l_Nat_repr(x_10);
x_21 = lean::string_append(x_19, x_20);
lean::dec(x_20);
x_22 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_23 = lean::string_append(x_21, x_22);
x_24 = l_Nat_repr(x_12);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
lean::cnstr_set_tag(x_4, 0);
lean::cnstr_set(x_4, 0, x_25);
return x_4;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_12);
lean::dec(x_10);
lean::free_heap_obj(x_4);
lean::dec(x_1);
x_26 = lean::mk_nat_obj(0u);
x_27 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_26, x_3);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_4, 0);
lean::inc(x_28);
lean::dec(x_4);
x_29 = lean::array_get_size(x_2);
x_30 = l_Lean_IR_Decl_params___main(x_28);
lean::dec(x_28);
x_31 = lean::array_get_size(x_30);
lean::dec(x_30);
x_32 = lean::nat_dec_lt(x_29, x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_1);
x_35 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_37 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_38 = lean::string_append(x_36, x_37);
x_39 = l_Nat_repr(x_29);
x_40 = lean::string_append(x_38, x_39);
lean::dec(x_39);
x_41 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_42 = lean::string_append(x_40, x_41);
x_43 = l_Nat_repr(x_31);
x_44 = lean::string_append(x_42, x_43);
lean::dec(x_43);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
lean::dec(x_29);
lean::dec(x_1);
x_46 = lean::mk_nat_obj(0u);
x_47 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_46, x_3);
return x_47;
}
}
}
}
}
obj* l_Lean_IR_Checker_checkPartialApp___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkExpr___main(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_Lean_IR_CtorInfo_isRef(x_4);
lean::dec(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_7, x_3);
lean::dec(x_5);
return x_8;
}
else
{
obj* x_9; 
x_9 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
lean::dec(x_5);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_9);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_13, x_3);
lean::dec(x_5);
return x_14;
}
}
}
case 2:
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
lean::dec(x_2);
x_17 = l_Lean_IR_Checker_checkObjVar(x_15, x_3);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
lean::dec(x_16);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_17);
x_21 = lean::mk_nat_obj(0u);
x_22 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_16, x_21, x_3);
lean::dec(x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
else
{
obj* x_26; 
lean::dec(x_22);
x_26 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_26;
}
}
}
case 4:
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
lean::dec(x_2);
x_28 = l_Lean_IR_Checker_checkObjVar(x_27, x_3);
if (lean::obj_tag(x_28) == 0)
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
lean::dec(x_28);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8 x_32; uint8 x_33; 
lean::dec(x_28);
x_32 = 5;
x_33 = l_Lean_IR_IRType_beq___main(x_1, x_32);
if (x_33 == 0)
{
obj* x_34; 
x_34 = l_Lean_IR_Checker_checkType___closed__1;
return x_34;
}
else
{
obj* x_35; 
x_35 = l_Lean_IR_Checker_checkVar___closed__2;
return x_35;
}
}
}
case 5:
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_2, 2);
lean::inc(x_36);
lean::dec(x_2);
x_37 = l_Lean_IR_Checker_checkObjVar(x_36, x_3);
if (lean::obj_tag(x_37) == 0)
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
lean::dec(x_37);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
}
else
{
obj* x_41; 
lean::dec(x_37);
x_41 = l_Lean_IR_Checker_checkScalarType(x_1, x_3);
return x_41;
}
}
case 6:
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = lean::cnstr_get(x_2, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_2, 1);
lean::inc(x_43);
lean::dec(x_2);
x_44 = l_Lean_IR_Checker_checkFullApp(x_42, x_43, x_3);
lean::dec(x_43);
return x_44;
}
case 7:
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_2, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_2, 1);
lean::inc(x_46);
lean::dec(x_2);
x_47 = l_Lean_IR_Checker_checkPartialApp(x_45, x_46, x_3);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
uint8 x_48; 
x_48 = !lean::is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
lean::dec(x_47);
x_50 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
else
{
obj* x_51; 
lean::dec(x_47);
x_51 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_51;
}
}
case 8:
{
obj* x_52; obj* x_53; obj* x_54; 
x_52 = lean::cnstr_get(x_2, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_2, 1);
lean::inc(x_53);
lean::dec(x_2);
x_54 = l_Lean_IR_Checker_checkObjVar(x_52, x_3);
if (lean::obj_tag(x_54) == 0)
{
uint8 x_55; 
lean::dec(x_53);
x_55 = !lean::is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
obj* x_56; obj* x_57; 
x_56 = lean::cnstr_get(x_54, 0);
lean::inc(x_56);
lean::dec(x_54);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_54);
x_58 = lean::mk_nat_obj(0u);
x_59 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_53, x_58, x_3);
lean::dec(x_53);
return x_59;
}
}
case 9:
{
uint8 x_60; obj* x_61; obj* x_62; 
x_60 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_61 = lean::cnstr_get(x_2, 0);
lean::inc(x_61);
lean::dec(x_2);
x_62 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
if (lean::obj_tag(x_62) == 0)
{
uint8 x_63; 
lean::dec(x_61);
x_63 = !lean::is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
obj* x_64; obj* x_65; 
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
lean::dec(x_62);
x_65 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
else
{
obj* x_66; 
lean::dec(x_62);
lean::inc(x_61);
x_66 = l_Lean_IR_Checker_checkScalarVar(x_61, x_3);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_67; 
lean::dec(x_61);
x_67 = !lean::is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
lean::dec(x_66);
x_69 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
uint8 x_70; 
x_70 = !lean::is_exclusive(x_66);
if (x_70 == 0)
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_66, 0);
lean::dec(x_71);
x_72 = lean::cnstr_get(x_3, 1);
x_73 = l_Lean_IR_LocalContext_getType(x_72, x_61);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_74 = l_Nat_repr(x_61);
x_75 = l_Lean_IR_VarId_HasToString___closed__1;
x_76 = lean::string_append(x_75, x_74);
lean::dec(x_74);
x_77 = l_Lean_IR_Checker_checkVar___closed__1;
x_78 = lean::string_append(x_77, x_76);
lean::dec(x_76);
x_79 = l_Char_HasRepr___closed__1;
x_80 = lean::string_append(x_78, x_79);
lean::cnstr_set_tag(x_66, 0);
lean::cnstr_set(x_66, 0, x_80);
return x_66;
}
else
{
obj* x_81; uint8 x_82; uint8 x_83; 
lean::free_heap_obj(x_66);
lean::dec(x_61);
x_81 = lean::cnstr_get(x_73, 0);
lean::inc(x_81);
lean::dec(x_73);
x_82 = lean::unbox(x_81);
lean::dec(x_81);
x_83 = l_Lean_IR_IRType_beq___main(x_82, x_60);
if (x_83 == 0)
{
obj* x_84; 
x_84 = l_Lean_IR_Checker_checkType___closed__1;
return x_84;
}
else
{
obj* x_85; 
x_85 = l_Lean_IR_Checker_checkVar___closed__2;
return x_85;
}
}
}
else
{
obj* x_86; obj* x_87; 
lean::dec(x_66);
x_86 = lean::cnstr_get(x_3, 1);
x_87 = l_Lean_IR_LocalContext_getType(x_86, x_61);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_88 = l_Nat_repr(x_61);
x_89 = l_Lean_IR_VarId_HasToString___closed__1;
x_90 = lean::string_append(x_89, x_88);
lean::dec(x_88);
x_91 = l_Lean_IR_Checker_checkVar___closed__1;
x_92 = lean::string_append(x_91, x_90);
lean::dec(x_90);
x_93 = l_Char_HasRepr___closed__1;
x_94 = lean::string_append(x_92, x_93);
x_95 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
else
{
obj* x_96; uint8 x_97; uint8 x_98; 
lean::dec(x_61);
x_96 = lean::cnstr_get(x_87, 0);
lean::inc(x_96);
lean::dec(x_87);
x_97 = lean::unbox(x_96);
lean::dec(x_96);
x_98 = l_Lean_IR_IRType_beq___main(x_97, x_60);
if (x_98 == 0)
{
obj* x_99; 
x_99 = l_Lean_IR_Checker_checkType___closed__1;
return x_99;
}
else
{
obj* x_100; 
x_100 = l_Lean_IR_Checker_checkVar___closed__2;
return x_100;
}
}
}
}
}
}
case 10:
{
obj* x_101; obj* x_102; 
x_101 = lean::cnstr_get(x_2, 0);
lean::inc(x_101);
lean::dec(x_2);
x_102 = l_Lean_IR_Checker_checkScalarType(x_1, x_3);
if (lean::obj_tag(x_102) == 0)
{
uint8 x_103; 
lean::dec(x_101);
x_103 = !lean::is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
obj* x_104; obj* x_105; 
x_104 = lean::cnstr_get(x_102, 0);
lean::inc(x_104);
lean::dec(x_102);
x_105 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
else
{
obj* x_106; 
lean::dec(x_102);
x_106 = l_Lean_IR_Checker_checkObjVar(x_101, x_3);
return x_106;
}
}
case 11:
{
obj* x_107; 
x_107 = lean::cnstr_get(x_2, 0);
lean::inc(x_107);
lean::dec(x_2);
if (lean::obj_tag(x_107) == 0)
{
obj* x_108; 
lean::dec(x_107);
x_108 = l_Lean_IR_Checker_checkVar___closed__2;
return x_108;
}
else
{
obj* x_109; 
lean::dec(x_107);
x_109 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_109;
}
}
case 12:
{
obj* x_110; obj* x_111; 
x_110 = lean::cnstr_get(x_2, 0);
lean::inc(x_110);
lean::dec(x_2);
x_111 = l_Lean_IR_Checker_checkObjVar(x_110, x_3);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
obj* x_113; obj* x_114; 
x_113 = lean::cnstr_get(x_111, 0);
lean::inc(x_113);
lean::dec(x_111);
x_114 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_114, 0, x_113);
return x_114;
}
}
else
{
uint8 x_115; uint8 x_116; 
lean::dec(x_111);
x_115 = 1;
x_116 = l_Lean_IR_IRType_beq___main(x_1, x_115);
if (x_116 == 0)
{
obj* x_117; 
x_117 = l_Lean_IR_Checker_checkType___closed__1;
return x_117;
}
else
{
obj* x_118; 
x_118 = l_Lean_IR_Checker_checkVar___closed__2;
return x_118;
}
}
}
case 13:
{
obj* x_119; obj* x_120; 
x_119 = lean::cnstr_get(x_2, 0);
lean::inc(x_119);
lean::dec(x_2);
x_120 = l_Lean_IR_Checker_checkObjVar(x_119, x_3);
if (lean::obj_tag(x_120) == 0)
{
uint8 x_121; 
x_121 = !lean::is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
obj* x_122; obj* x_123; 
x_122 = lean::cnstr_get(x_120, 0);
lean::inc(x_122);
lean::dec(x_120);
x_123 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_123, 0, x_122);
return x_123;
}
}
else
{
uint8 x_124; uint8 x_125; 
lean::dec(x_120);
x_124 = 1;
x_125 = l_Lean_IR_IRType_beq___main(x_1, x_124);
if (x_125 == 0)
{
obj* x_126; 
x_126 = l_Lean_IR_Checker_checkType___closed__1;
return x_126;
}
else
{
obj* x_127; 
x_127 = l_Lean_IR_Checker_checkVar___closed__2;
return x_127;
}
}
}
default: 
{
obj* x_128; obj* x_129; 
x_128 = lean::cnstr_get(x_2, 1);
lean::inc(x_128);
lean::dec(x_2);
x_129 = l_Lean_IR_Checker_checkObjVar(x_128, x_3);
if (lean::obj_tag(x_129) == 0)
{
uint8 x_130; 
x_130 = !lean::is_exclusive(x_129);
if (x_130 == 0)
{
return x_129;
}
else
{
obj* x_131; obj* x_132; 
x_131 = lean::cnstr_get(x_129, 0);
lean::inc(x_131);
lean::dec(x_129);
x_132 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
return x_132;
}
}
else
{
obj* x_133; 
lean::dec(x_129);
x_133 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_133;
}
}
}
}
}
obj* l_Lean_IR_Checker_checkExpr___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_IR_Checker_checkExpr___main(x_4, x_2, x_3);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_Checker_checkExpr(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_checkExpr___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkExpr___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_IR_Checker_checkExpr(x_4, x_2, x_3);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("invalid parameter declaration, shadowing is not allowed");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_16;
}
}
}
}
obj* l_Lean_IR_Checker_withParams(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_1, x_1, x_7, x_5, x_3);
x_9 = !lean::is_exclusive(x_3);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_3, 2);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_3, 1);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_3, 0);
lean::dec(x_12);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_13; 
lean::free_heap_obj(x_3);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_13 = !lean::is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_8, 0);
lean::inc(x_16);
lean::dec(x_8);
lean::cnstr_set(x_3, 1, x_16);
x_17 = lean::apply_1(x_2, x_3);
return x_17;
}
}
else
{
lean::dec(x_3);
if (lean::obj_tag(x_8) == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_19 = x_8;
} else {
 lean::dec_ref(x_8);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
lean::dec(x_8);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_4);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set(x_22, 2, x_6);
x_23 = lean::apply_1(x_2, x_22);
return x_23;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_IR_Checker_withParams___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Checker_withParams(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_16;
}
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_2);
x_6 = l_Lean_IR_Checker_checkVar___closed__2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_1, x_2);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_2, x_8);
lean::dec(x_2);
x_10 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
lean::inc(x_3);
x_11 = l_Lean_IR_Checker_checkFnBody___main(x_10, x_3);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
lean::dec(x_9);
lean::dec(x_3);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean::dec(x_11);
x_2 = x_9;
goto _start;
}
}
}
}
obj* _init_l_Lean_IR_Checker_checkFnBody___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("invalid variable declaration, shadowing is not allowed");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_Checker_checkFnBody___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("invalid join point declaration, shadowing is not allowed");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Checker_checkFnBody___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_5);
x_7 = l_Lean_IR_Checker_checkExpr___main(x_4, x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8 x_11; 
lean::dec(x_7);
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_12 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_2, 1);
x_14 = lean::cnstr_get(x_2, 2);
x_15 = l_Lean_IR_LocalContext_contains(x_13, x_3);
if (x_15 == 0)
{
obj* x_16; 
x_16 = l_Lean_IR_LocalContext_addLocal(x_13, x_3, x_4, x_5);
lean::cnstr_set(x_2, 1, x_16);
x_1 = x_6;
goto _start;
}
else
{
obj* x_18; 
lean::free_heap_obj(x_2);
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_18 = l_Lean_IR_Checker_checkFnBody___main___closed__1;
return x_18;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_19 = lean::cnstr_get(x_2, 0);
x_20 = lean::cnstr_get(x_2, 1);
x_21 = lean::cnstr_get(x_2, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_2);
x_22 = l_Lean_IR_LocalContext_contains(x_20, x_3);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = l_Lean_IR_LocalContext_addLocal(x_20, x_3, x_4, x_5);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set(x_24, 2, x_21);
x_1 = x_6;
x_2 = x_24;
goto _start;
}
else
{
obj* x_26; 
lean::dec(x_21);
lean::dec(x_20);
lean::dec(x_19);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_26 = l_Lean_IR_Checker_checkFnBody___main___closed__1;
return x_26;
}
}
}
}
case 1:
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_1, 1);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_1, 2);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_1, 3);
lean::inc(x_30);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_2, 1);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_2, 2);
lean::inc(x_33);
x_34 = lean::mk_nat_obj(0u);
lean::inc(x_32);
x_35 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_28, x_28, x_34, x_32, x_2);
x_36 = !lean::is_exclusive(x_2);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_2, 2);
lean::dec(x_37);
x_38 = lean::cnstr_get(x_2, 1);
lean::dec(x_38);
x_39 = lean::cnstr_get(x_2, 0);
lean::dec(x_39);
if (lean::obj_tag(x_35) == 0)
{
uint8 x_40; 
lean::free_heap_obj(x_2);
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
lean::dec(x_27);
x_40 = !lean::is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
else
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_35, 0);
lean::inc(x_43);
lean::dec(x_35);
lean::inc(x_33);
lean::inc(x_31);
lean::cnstr_set(x_2, 1, x_43);
lean::inc(x_29);
x_44 = l_Lean_IR_Checker_checkFnBody___main(x_29, x_2);
if (lean::obj_tag(x_44) == 0)
{
uint8 x_45; 
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
lean::dec(x_27);
x_45 = !lean::is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_44, 0);
lean::inc(x_46);
lean::dec(x_44);
x_47 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8 x_48; 
lean::dec(x_44);
x_48 = l_Lean_IR_LocalContext_contains(x_32, x_27);
if (x_48 == 0)
{
obj* x_49; obj* x_50; 
x_49 = l_Lean_IR_LocalContext_addJP(x_32, x_27, x_28, x_29);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_31);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_50, 2, x_33);
x_1 = x_30;
x_2 = x_50;
goto _start;
}
else
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
lean::dec(x_27);
x_52 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_52;
}
}
}
}
else
{
lean::dec(x_2);
if (lean::obj_tag(x_35) == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
lean::dec(x_27);
x_53 = lean::cnstr_get(x_35, 0);
lean::inc(x_53);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_54 = x_35;
} else {
 lean::dec_ref(x_35);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_53);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_35, 0);
lean::inc(x_56);
lean::dec(x_35);
lean::inc(x_33);
lean::inc(x_31);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_31);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set(x_57, 2, x_33);
lean::inc(x_29);
x_58 = l_Lean_IR_Checker_checkFnBody___main(x_29, x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
lean::dec(x_27);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_60 = x_58;
} else {
 lean::dec_ref(x_58);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_59);
return x_61;
}
else
{
uint8 x_62; 
lean::dec(x_58);
x_62 = l_Lean_IR_LocalContext_contains(x_32, x_27);
if (x_62 == 0)
{
obj* x_63; obj* x_64; 
x_63 = l_Lean_IR_LocalContext_addJP(x_32, x_27, x_28, x_29);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_31);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set(x_64, 2, x_33);
x_1 = x_30;
x_2 = x_64;
goto _start;
}
else
{
obj* x_66; 
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
lean::dec(x_27);
x_66 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_66;
}
}
}
}
}
case 2:
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_1, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_1, 2);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_1, 3);
lean::inc(x_69);
lean::dec(x_1);
x_70 = l_Lean_IR_Checker_checkVar(x_67, x_2);
if (lean::obj_tag(x_70) == 0)
{
uint8 x_71; 
lean::dec(x_69);
lean::dec(x_68);
lean::dec(x_2);
x_71 = !lean::is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
obj* x_72; obj* x_73; 
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
lean::dec(x_70);
x_73 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
else
{
obj* x_74; 
lean::dec(x_70);
x_74 = l_Lean_IR_Checker_checkArg(x_68, x_2);
if (lean::obj_tag(x_74) == 0)
{
uint8 x_75; 
lean::dec(x_69);
lean::dec(x_2);
x_75 = !lean::is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
obj* x_76; obj* x_77; 
x_76 = lean::cnstr_get(x_74, 0);
lean::inc(x_76);
lean::dec(x_74);
x_77 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean::dec(x_74);
x_1 = x_69;
goto _start;
}
}
}
case 4:
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_79 = lean::cnstr_get(x_1, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_1, 2);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_1, 3);
lean::inc(x_81);
lean::dec(x_1);
x_82 = l_Lean_IR_Checker_checkVar(x_79, x_2);
if (lean::obj_tag(x_82) == 0)
{
uint8 x_83; 
lean::dec(x_81);
lean::dec(x_80);
lean::dec(x_2);
x_83 = !lean::is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
lean::dec(x_82);
x_85 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
}
else
{
obj* x_86; 
lean::dec(x_82);
x_86 = l_Lean_IR_Checker_checkVar(x_80, x_2);
if (lean::obj_tag(x_86) == 0)
{
uint8 x_87; 
lean::dec(x_81);
lean::dec(x_2);
x_87 = !lean::is_exclusive(x_86);
if (x_87 == 0)
{
return x_86;
}
else
{
obj* x_88; obj* x_89; 
x_88 = lean::cnstr_get(x_86, 0);
lean::inc(x_88);
lean::dec(x_86);
x_89 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
}
else
{
lean::dec(x_86);
x_1 = x_81;
goto _start;
}
}
}
case 5:
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_1, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_1, 3);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_1, 4);
lean::inc(x_93);
lean::dec(x_1);
x_94 = l_Lean_IR_Checker_checkVar(x_91, x_2);
if (lean::obj_tag(x_94) == 0)
{
uint8 x_95; 
lean::dec(x_93);
lean::dec(x_92);
lean::dec(x_2);
x_95 = !lean::is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
obj* x_96; obj* x_97; 
x_96 = lean::cnstr_get(x_94, 0);
lean::inc(x_96);
lean::dec(x_94);
x_97 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
else
{
obj* x_98; 
lean::dec(x_94);
x_98 = l_Lean_IR_Checker_checkVar(x_92, x_2);
if (lean::obj_tag(x_98) == 0)
{
uint8 x_99; 
lean::dec(x_93);
lean::dec(x_2);
x_99 = !lean::is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
obj* x_100; obj* x_101; 
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
lean::dec(x_98);
x_101 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
else
{
lean::dec(x_98);
x_1 = x_93;
goto _start;
}
}
}
case 8:
{
obj* x_103; obj* x_104; obj* x_105; 
x_103 = lean::cnstr_get(x_1, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_1, 1);
lean::inc(x_104);
lean::dec(x_1);
x_105 = l_Lean_IR_Checker_checkVar(x_103, x_2);
if (lean::obj_tag(x_105) == 0)
{
uint8 x_106; 
lean::dec(x_104);
lean::dec(x_2);
x_106 = !lean::is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
obj* x_107; obj* x_108; 
x_107 = lean::cnstr_get(x_105, 0);
lean::inc(x_107);
lean::dec(x_105);
x_108 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
}
else
{
lean::dec(x_105);
x_1 = x_104;
goto _start;
}
}
case 9:
{
obj* x_110; 
x_110 = lean::cnstr_get(x_1, 1);
lean::inc(x_110);
lean::dec(x_1);
x_1 = x_110;
goto _start;
}
case 10:
{
obj* x_112; obj* x_113; obj* x_114; 
x_112 = lean::cnstr_get(x_1, 1);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_1, 2);
lean::inc(x_113);
lean::dec(x_1);
x_114 = l_Lean_IR_Checker_checkVar(x_112, x_2);
if (lean::obj_tag(x_114) == 0)
{
uint8 x_115; 
lean::dec(x_113);
lean::dec(x_2);
x_115 = !lean::is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
obj* x_116; obj* x_117; 
x_116 = lean::cnstr_get(x_114, 0);
lean::inc(x_116);
lean::dec(x_114);
x_117 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
return x_117;
}
}
else
{
obj* x_118; obj* x_119; 
lean::dec(x_114);
x_118 = lean::mk_nat_obj(0u);
x_119 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_113, x_118, x_2);
lean::dec(x_113);
return x_119;
}
}
case 11:
{
obj* x_120; obj* x_121; 
x_120 = lean::cnstr_get(x_1, 0);
lean::inc(x_120);
lean::dec(x_1);
x_121 = l_Lean_IR_Checker_checkArg(x_120, x_2);
lean::dec(x_2);
return x_121;
}
case 12:
{
obj* x_122; obj* x_123; obj* x_124; 
x_122 = lean::cnstr_get(x_1, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_1, 1);
lean::inc(x_123);
lean::dec(x_1);
x_124 = l_Lean_IR_Checker_checkJP(x_122, x_2);
if (lean::obj_tag(x_124) == 0)
{
uint8 x_125; 
lean::dec(x_123);
lean::dec(x_2);
x_125 = !lean::is_exclusive(x_124);
if (x_125 == 0)
{
return x_124;
}
else
{
obj* x_126; obj* x_127; 
x_126 = lean::cnstr_get(x_124, 0);
lean::inc(x_126);
lean::dec(x_124);
x_127 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
}
else
{
obj* x_128; obj* x_129; 
lean::dec(x_124);
x_128 = lean::mk_nat_obj(0u);
x_129 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_123, x_128, x_2);
lean::dec(x_2);
lean::dec(x_123);
return x_129;
}
}
case 13:
{
obj* x_130; 
lean::dec(x_2);
x_130 = l_Lean_IR_Checker_checkVar___closed__2;
return x_130;
}
default: 
{
obj* x_131; obj* x_132; obj* x_133; 
x_131 = lean::cnstr_get(x_1, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_1, 2);
lean::inc(x_132);
lean::dec(x_1);
x_133 = l_Lean_IR_Checker_checkVar(x_131, x_2);
if (lean::obj_tag(x_133) == 0)
{
uint8 x_134; 
lean::dec(x_132);
lean::dec(x_2);
x_134 = !lean::is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
obj* x_135; obj* x_136; 
x_135 = lean::cnstr_get(x_133, 0);
lean::inc(x_135);
lean::dec(x_133);
x_136 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean::dec(x_133);
x_1 = x_132;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Checker_checkFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_16;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
return x_16;
}
}
}
}
obj* l_Lean_IR_Checker_checkDecl___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(x_3, x_3, x_8, x_6, x_2);
lean::dec(x_3);
x_10 = !lean::is_exclusive(x_2);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 2);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_2, 1);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_2, 0);
lean::dec(x_13);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_14; 
lean::free_heap_obj(x_2);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_14 = !lean::is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
lean::dec(x_9);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_9, 0);
lean::inc(x_17);
lean::dec(x_9);
lean::cnstr_set(x_2, 1, x_17);
x_18 = l_Lean_IR_Checker_checkFnBody___main(x_4, x_2);
return x_18;
}
}
else
{
lean::dec(x_2);
if (lean::obj_tag(x_9) == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_20 = x_9;
} else {
 lean::dec_ref(x_9);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_19);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_9, 0);
lean::inc(x_22);
lean::dec(x_9);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_23, 2, x_7);
x_24 = l_Lean_IR_Checker_checkFnBody___main(x_4, x_23);
return x_24;
}
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::dec(x_1);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::cnstr_get(x_2, 1);
lean::inc(x_28);
x_29 = lean::mk_nat_obj(0u);
x_30 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(x_25, x_25, x_29, x_28, x_2);
lean::dec(x_2);
lean::dec(x_25);
if (lean::obj_tag(x_30) == 0)
{
uint8 x_31; 
lean::dec(x_27);
x_31 = !lean::is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
lean::dec(x_30);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean::dec(x_30);
return x_27;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_IR_Checker_checkDecl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Checker_checkDecl___main(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_checkDecl___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("IR check failed at '");
return x_1;
}
}
obj* _init_l_Lean_IR_checkDecl___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("', error: ");
return x_1;
}
}
obj* l_Lean_IR_checkDecl(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_getEnv___rarg(x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_1);
lean::inc(x_2);
x_10 = l_Lean_IR_Checker_checkDecl___main(x_2, x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = l_Lean_IR_Decl_name___main(x_2);
lean::dec(x_2);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_12);
x_15 = l_Lean_IR_checkDecl___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_17 = l_Lean_IR_checkDecl___closed__2;
x_18 = lean::string_append(x_16, x_17);
x_19 = lean::string_append(x_18, x_11);
lean::dec(x_11);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_19);
return x_5;
}
else
{
obj* x_20; 
lean::dec(x_10);
lean::dec(x_2);
x_20 = lean::box(0);
lean::cnstr_set(x_5, 0, x_20);
return x_5;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_5, 0);
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_5);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set(x_24, 2, x_1);
lean::inc(x_2);
x_25 = l_Lean_IR_Checker_checkDecl___main(x_2, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_27 = l_Lean_IR_Decl_name___main(x_2);
lean::dec(x_2);
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_27);
x_30 = l_Lean_IR_checkDecl___closed__1;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_32 = l_Lean_IR_checkDecl___closed__2;
x_33 = lean::string_append(x_31, x_32);
x_34 = lean::string_append(x_33, x_26);
lean::dec(x_26);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_22);
return x_35;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_25);
lean::dec(x_2);
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_22);
return x_37;
}
}
}
else
{
uint8 x_38; 
lean::dec(x_2);
lean::dec(x_1);
x_38 = !lean::is_exclusive(x_5);
if (x_38 == 0)
{
return x_5;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_5, 0);
x_40 = lean::cnstr_get(x_5, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_5);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
}
obj* l_Lean_IR_checkDecl___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_3);
lean::dec(x_1);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 0);
lean::dec(x_9);
x_10 = lean::box(0);
lean::cnstr_set(x_5, 0, x_10);
return x_5;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
lean::dec(x_5);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::array_fget(x_2, x_3);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
lean::inc(x_1);
x_17 = l_Lean_IR_checkDecl(x_1, x_14, x_4, x_5);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::dec(x_19);
x_20 = lean::box(0);
lean::cnstr_set(x_17, 0, x_20);
x_3 = x_16;
x_5 = x_17;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_3 = x_16;
x_5 = x_24;
goto _start;
}
}
else
{
uint8 x_26; 
lean::dec(x_16);
lean::dec(x_1);
x_26 = !lean::is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_17, 0);
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_17);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Lean_IR_checkDecls(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_5 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_4, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_IR_checkDecls___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "getDecl"), 2, l_Lean_IR_Checker_getDecl___boxed);
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkVar"), 2, l_Lean_IR_Checker_checkVar___boxed);
l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkJP"), 2, l_Lean_IR_Checker_checkJP___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkArg"), 2, l_Lean_IR_Checker_checkArg___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkArgs"), 2, l_Lean_IR_Checker_checkArgs___boxed);
l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkType"), 3, l_Lean_IR_Checker_checkType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkObjType"), 2, l_Lean_IR_Checker_checkObjType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkScalarType"), 2, l_Lean_IR_Checker_checkScalarType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkVarType"), 3, l_Lean_IR_Checker_checkVarType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkObjVar"), 2, l_Lean_IR_Checker_checkObjVar___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkScalarVar"), 2, l_Lean_IR_Checker_checkScalarVar___boxed);
l_Lean_IR_Checker_checkFullApp___closed__1 = _init_l_Lean_IR_Checker_checkFullApp___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__1);
l_Lean_IR_Checker_checkFullApp___closed__2 = _init_l_Lean_IR_Checker_checkFullApp___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__2);
l_Lean_IR_Checker_checkFullApp___closed__3 = _init_l_Lean_IR_Checker_checkFullApp___closed__3();
lean::mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkFullApp"), 3, l_Lean_IR_Checker_checkFullApp___boxed);
l_Lean_IR_Checker_checkPartialApp___closed__1 = _init_l_Lean_IR_Checker_checkPartialApp___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__1);
l_Lean_IR_Checker_checkPartialApp___closed__2 = _init_l_Lean_IR_Checker_checkPartialApp___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__2);
l_Lean_IR_Checker_checkPartialApp___closed__3 = _init_l_Lean_IR_Checker_checkPartialApp___closed__3();
lean::mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkPartialApp"), 3, l_Lean_IR_Checker_checkPartialApp___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkExpr"), 3, l_Lean_IR_Checker_checkExpr___boxed);
l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1 = _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1();
lean::mark_persistent(l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "withParams"), 3, l_Lean_IR_Checker_withParams___boxed);
l_Lean_IR_Checker_checkFnBody___main___closed__1 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__1);
l_Lean_IR_Checker_checkFnBody___main___closed__2 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__2();
lean::mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkFnBody"), 2, l_Lean_IR_Checker_checkFnBody);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "Checker"), "checkDecl"), 2, l_Lean_IR_Checker_checkDecl);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean::mark_persistent(l_Lean_IR_checkDecl___closed__1);
l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean::mark_persistent(l_Lean_IR_checkDecl___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "checkDecl"), 4, l_Lean_IR_checkDecl___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "checkDecls"), 3, l_Lean_IR_checkDecls___boxed);
return w;
}
