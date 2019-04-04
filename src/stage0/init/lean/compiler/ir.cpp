// Lean compiler output
// Module: init.lean.compiler.ir
// Imports: init.default init.lean.name init.lean.kvmap
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
uint8 l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_Litval_beq___main___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
uint8 l_Lean_IR_IRType_beq(uint8, uint8);
uint8 l_Lean_IR_Arg_alphaEqv(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_10__collectFnBody(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_addParamRename(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_HasBeq;
obj* l___private_init_lean_compiler_ir_8__collectExpr___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_3__withBv(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_10__collectFnBody___main(obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_insertParams(obj*, obj*);
uint8 l_Lean_IR_Fnbody_beq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_8__collectExpr(obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_beq(obj*, obj*);
obj* l_Lean_IR_Fnbody_HasBeq;
uint8 l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1(uint8, obj*);
obj* l_Lean_IR_Alt_default(obj*);
obj* l_Lean_IR_Fnbody_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Fnbody_isPure___main___boxed(obj*);
uint8 l_Lean_IR_Fnbody_isPure___main(obj*);
obj* l_Lean_IR_VarId_hasAeqv;
uint8 l_Lean_NameSet_contains(obj*, obj*);
uint8 l_Lean_IR_Expr_isPure___main(obj*);
obj* l___private_init_lean_compiler_ir_1__skip___boxed(obj*);
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_2__collectVar(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip(obj*);
obj* l___private_init_lean_compiler_ir_6__collectArg___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_6__collectArg(obj*, obj*, obj*);
obj* l_Lean_IR_freeVars(obj*);
uint8 l_Lean_IR_Litval_beq(obj*, obj*);
obj* l_Lean_IR_addParamsRename(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_args_hasAeqv;
obj* l_Lean_IR_args_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Expr_alphaEqv(obj*, obj*, obj*);
uint8 l_Lean_IR_Fnbody_alphaEqv(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_Litval_HasBeq;
uint8 l_Lean_IR_Litval_beq___main(obj*, obj*);
uint8 l_Lean_KVMap_eqv(obj*, obj*);
obj* l_Lean_IR_Expr_hasAeqv;
obj* l_Lean_IR_args_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_HasBeq;
obj* l_Lean_NameMap_insert___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___boxed(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_Litval_beq___boxed(obj*, obj*);
obj* l_Lean_IR_HasAndthen;
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArgs___main(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___main___boxed(obj*);
obj* l___private_init_lean_compiler_ir_5__seq(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_addVarRename(obj*, obj*, obj*);
obj* l_Lean_IR_Fnbody_isPure___boxed(obj*);
uint8 l_Lean_IR_Arg_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Fnbody_alphaEqv___main(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
uint8 l_Lean_IR_CtorInfo_beq___main(obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArgs(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___main___boxed(obj*, obj*);
uint8 l_Lean_IR_Expr_alphaEqv___main(obj*, obj*, obj*);
uint8 l_Lean_IR_Expr_isPure(obj*);
obj* l_List_foldl___main___at_Lean_IR_insertParams___spec__1(obj*, obj*);
obj* l_Lean_IR_Arg_hasAeqv;
obj* l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Alt_ctor(obj*, obj*);
obj* l_Lean_IR_MData_HasEmptyc;
obj* l_Lean_IR_IRType_beq___boxed(obj*, obj*);
obj* l_Lean_NameSet_insert(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg___boxed(obj*);
obj* l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1;
obj* l_Lean_IR_Fnbody_beq___boxed(obj*, obj*);
uint8 l_Lean_IR_Fnbody_isPure(obj*);
obj* l___private_init_lean_compiler_ir_4__withParams(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___boxed(obj*, obj*);
obj* l_Lean_IR_MData_empty;
obj* l___private_init_lean_compiler_ir_9__collectAlts___main(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_9__collectAlts(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_IRType_beq___main___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg(obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
obj* l_Lean_IR_Fnbody_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* _init_l_Lean_IR_MData_empty() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_IR_MData_HasEmptyc() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_Lean_IR_IRType_beq___main(uint8 x_0, uint8 x_1) {
_start:
{
switch (x_0) {
case 0:
{
switch (x_1) {
case 0:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
default:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
case 1:
{
switch (x_1) {
case 1:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
default:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
case 2:
{
switch (x_1) {
case 2:
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
case 3:
{
switch (x_1) {
case 3:
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
default:
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
}
}
case 4:
{
switch (x_1) {
case 4:
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
default:
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
}
}
case 5:
{
switch (x_1) {
case 5:
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
default:
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
}
}
case 6:
{
switch (x_1) {
case 6:
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
case 7:
{
switch (x_1) {
case 7:
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
default:
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
}
}
default:
{
switch (x_1) {
case 8:
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
default:
{
uint8 x_19; 
x_19 = 0;
return x_19;
}
}
}
}
}
}
obj* l_Lean_IR_IRType_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_IRType_beq___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Lean_IR_IRType_beq(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_IRType_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_IRType_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_IRType_beq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_Lean_IR_IRType_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_IRType_beq___boxed), 2, 0);
return x_0;
}
}
uint8 l_Lean_IR_Litval_beq___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::nat_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::string_dec_eq(x_7, x_8);
return x_9;
}
}
}
}
obj* l_Lean_IR_Litval_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Litval_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_Litval_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_Litval_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Litval_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Litval_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_Litval_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Litval_beq___boxed), 2, 0);
return x_0;
}
}
uint8 l_Lean_IR_CtorInfo_beq___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::cnstr_get(x_0, 3);
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
x_10 = lean_name_dec_eq(x_2, x_6);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = lean::nat_dec_eq(x_3, x_7);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8 x_14; 
x_14 = lean::nat_dec_eq(x_4, x_8);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::nat_dec_eq(x_5, x_9);
return x_16;
}
}
}
}
}
obj* l_Lean_IR_CtorInfo_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_CtorInfo_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_CtorInfo_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_CtorInfo_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_CtorInfo_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_CtorInfo_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_CtorInfo_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_CtorInfo_beq___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_IR_Alt_ctor(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_IR_Alt_default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
uint8 l_Lean_IR_Expr_isPure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 2:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 9:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 10:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
case 12:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
case 13:
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_Lean_IR_Expr_isPure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Expr_isPure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_Expr_isPure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Expr_isPure___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Expr_isPure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Expr_isPure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1(uint8 x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1(x_0, x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_Lean_IR_Fnbody_isPure___main(x_5);
if (x_6 == 0)
{
return x_4;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
else
{
return x_4;
}
}
}
}
uint8 l_Lean_IR_Fnbody_isPure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::cnstr_get(x_0, 2);
x_3 = l_Lean_IR_Expr_isPure___main(x_1);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
x_0 = x_2;
goto _start;
}
}
case 1:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
x_8 = l_Lean_IR_Fnbody_isPure___main(x_6);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
x_0 = x_7;
goto _start;
}
}
case 3:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 3);
x_0 = x_11;
goto _start;
}
case 4:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 4);
x_0 = x_13;
goto _start;
}
case 8:
{
obj* x_15; 
x_15 = lean::cnstr_get(x_0, 1);
x_0 = x_15;
goto _start;
}
case 9:
{
obj* x_17; uint8 x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_0, 2);
x_18 = 0;
x_19 = l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1(x_18, x_17);
return x_19;
}
case 10:
{
uint8 x_20; 
x_20 = 1;
return x_20;
}
case 11:
{
uint8 x_21; 
x_21 = 1;
return x_21;
}
case 12:
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
default:
{
uint8 x_23; 
x_23 = 0;
return x_23;
}
}
}
}
obj* l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_List_foldr___main___at_Lean_IR_Fnbody_isPure___main___spec__1(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Fnbody_isPure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Fnbody_isPure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_Fnbody_isPure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Fnbody_isPure___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Fnbody_isPure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Fnbody_isPure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
uint8 l_Lean_IR_VarId_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = lean_name_dec_eq(x_1, x_2);
return x_4;
}
else
{
obj* x_5; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean_name_dec_eq(x_5, x_2);
lean::dec(x_5);
return x_8;
}
}
}
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_VarId_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_VarId_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_VarId_alphaEqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_Lean_IR_Arg_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = l_Lean_IR_VarId_alphaEqv(x_0, x_3, x_4);
return x_5;
}
else
{
uint8 x_7; 
lean::dec(x_0);
x_7 = 0;
return x_7;
}
}
else
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
}
}
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Lean_IR_Arg_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Arg_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_Arg_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Arg_alphaEqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_Lean_IR_args_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_7; 
lean::dec(x_0);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_13 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_8, x_10);
if (x_13 == 0)
{
uint8 x_15; 
lean::dec(x_0);
x_15 = 0;
return x_15;
}
else
{
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_args_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_args_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Lean_IR_args_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_args_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_args_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_args_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_args_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_args_alphaEqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_Lean_IR_Expr_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_IR_CtorInfo_beq___main(x_3, x_5);
if (x_7 == 0)
{
uint8 x_9; 
lean::dec(x_0);
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
x_10 = l_Lean_IR_args_alphaEqv___main(x_0, x_4, x_6);
return x_10;
}
}
default:
{
uint8 x_12; 
lean::dec(x_0);
x_12 = 0;
return x_12;
}
}
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_2, 0);
x_15 = l_Lean_IR_VarId_alphaEqv(x_0, x_13, x_14);
return x_15;
}
default:
{
uint8 x_17; 
lean::dec(x_0);
x_17 = 0;
return x_17;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_25; 
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_20 = lean::cnstr_get(x_1, 2);
x_21 = lean::cnstr_get(x_2, 0);
x_22 = lean::cnstr_get(x_2, 1);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_25 = l_Lean_IR_VarId_alphaEqv(x_0, x_18, x_21);
if (x_25 == 0)
{
uint8 x_27; 
lean::dec(x_0);
x_27 = 0;
return x_27;
}
else
{
uint8 x_28; 
x_28 = l_Lean_IR_CtorInfo_beq___main(x_19, x_22);
if (x_28 == 0)
{
uint8 x_30; 
lean::dec(x_0);
x_30 = 0;
return x_30;
}
else
{
uint8 x_31; 
x_31 = l_Lean_IR_args_alphaEqv___main(x_0, x_20, x_23);
return x_31;
}
}
}
default:
{
uint8 x_33; 
lean::dec(x_0);
x_33 = 0;
return x_33;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_34 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get(x_1, 1);
x_36 = lean::cnstr_get(x_2, 0);
x_37 = lean::cnstr_get(x_2, 1);
x_38 = lean::nat_dec_eq(x_34, x_36);
if (x_38 == 0)
{
uint8 x_40; 
lean::dec(x_0);
x_40 = 0;
return x_40;
}
else
{
uint8 x_41; 
x_41 = l_Lean_IR_VarId_alphaEqv(x_0, x_35, x_37);
return x_41;
}
}
default:
{
uint8 x_43; 
lean::dec(x_0);
x_43 = 0;
return x_43;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_1, 0);
x_45 = lean::cnstr_get(x_1, 1);
x_46 = lean::cnstr_get(x_2, 0);
x_47 = lean::cnstr_get(x_2, 1);
x_48 = lean::nat_dec_eq(x_44, x_46);
if (x_48 == 0)
{
uint8 x_50; 
lean::dec(x_0);
x_50 = 0;
return x_50;
}
else
{
uint8 x_51; 
x_51 = l_Lean_IR_VarId_alphaEqv(x_0, x_45, x_47);
return x_51;
}
}
default:
{
uint8 x_53; 
lean::dec(x_0);
x_53 = 0;
return x_53;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_1, 0);
x_55 = lean::cnstr_get(x_1, 1);
x_56 = lean::cnstr_get(x_2, 0);
x_57 = lean::cnstr_get(x_2, 1);
x_58 = lean::nat_dec_eq(x_54, x_56);
if (x_58 == 0)
{
uint8 x_60; 
lean::dec(x_0);
x_60 = 0;
return x_60;
}
else
{
uint8 x_61; 
x_61 = l_Lean_IR_VarId_alphaEqv(x_0, x_55, x_57);
return x_61;
}
}
default:
{
uint8 x_63; 
lean::dec(x_0);
x_63 = 0;
return x_63;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; 
x_64 = lean::cnstr_get(x_1, 0);
x_65 = lean::cnstr_get(x_1, 1);
x_66 = lean::cnstr_get(x_2, 0);
x_67 = lean::cnstr_get(x_2, 1);
x_68 = lean_name_dec_eq(x_64, x_66);
if (x_68 == 0)
{
uint8 x_70; 
lean::dec(x_0);
x_70 = 0;
return x_70;
}
else
{
uint8 x_71; 
x_71 = l_Lean_IR_args_alphaEqv___main(x_0, x_65, x_67);
return x_71;
}
}
default:
{
uint8 x_73; 
lean::dec(x_0);
x_73 = 0;
return x_73;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_74; obj* x_75; obj* x_76; uint8 x_77; 
x_74 = lean::cnstr_get(x_1, 0);
x_75 = lean::cnstr_get(x_2, 0);
x_76 = lean::cnstr_get(x_2, 1);
x_77 = lean_name_dec_eq(x_74, x_75);
if (x_77 == 0)
{
uint8 x_79; 
lean::dec(x_0);
x_79 = 0;
return x_79;
}
else
{
uint8 x_80; 
x_80 = l_Lean_IR_args_alphaEqv___main(x_0, x_76, x_76);
return x_80;
}
}
default:
{
uint8 x_82; 
lean::dec(x_0);
x_82 = 0;
return x_82;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; uint8 x_88; 
x_83 = lean::cnstr_get(x_1, 0);
x_84 = lean::cnstr_get(x_1, 1);
x_85 = lean::cnstr_get(x_2, 0);
x_86 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_88 = l_Lean_IR_VarId_alphaEqv(x_0, x_83, x_85);
if (x_88 == 0)
{
uint8 x_90; 
lean::dec(x_0);
x_90 = 0;
return x_90;
}
else
{
uint8 x_91; 
x_91 = l_Lean_IR_args_alphaEqv___main(x_0, x_84, x_86);
return x_91;
}
}
default:
{
uint8 x_93; 
lean::dec(x_0);
x_93 = 0;
return x_93;
}
}
}
case 9:
{
uint8 x_94; 
x_94 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_95; uint8 x_96; obj* x_97; uint8 x_98; 
x_95 = lean::cnstr_get(x_1, 0);
x_96 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_97 = lean::cnstr_get(x_2, 0);
x_98 = l_Lean_IR_IRType_beq___main(x_94, x_96);
if (x_98 == 0)
{
uint8 x_100; 
lean::dec(x_0);
x_100 = 0;
return x_100;
}
else
{
uint8 x_101; 
x_101 = l_Lean_IR_VarId_alphaEqv(x_0, x_95, x_97);
return x_101;
}
}
default:
{
uint8 x_103; 
lean::dec(x_0);
x_103 = 0;
return x_103;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_104; obj* x_105; uint8 x_106; 
x_104 = lean::cnstr_get(x_1, 0);
x_105 = lean::cnstr_get(x_2, 0);
x_106 = l_Lean_IR_VarId_alphaEqv(x_0, x_104, x_105);
return x_106;
}
default:
{
uint8 x_108; 
lean::dec(x_0);
x_108 = 0;
return x_108;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_110; obj* x_111; uint8 x_112; 
x_110 = lean::cnstr_get(x_1, 0);
x_111 = lean::cnstr_get(x_2, 0);
x_112 = l_Lean_IR_Litval_beq___main(x_110, x_111);
return x_112;
}
default:
{
uint8 x_113; 
x_113 = 0;
return x_113;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_114; obj* x_115; uint8 x_116; 
x_114 = lean::cnstr_get(x_1, 0);
x_115 = lean::cnstr_get(x_2, 0);
x_116 = l_Lean_IR_VarId_alphaEqv(x_0, x_114, x_115);
return x_116;
}
default:
{
uint8 x_118; 
lean::dec(x_0);
x_118 = 0;
return x_118;
}
}
}
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_119; obj* x_120; uint8 x_121; 
x_119 = lean::cnstr_get(x_1, 0);
x_120 = lean::cnstr_get(x_2, 0);
x_121 = l_Lean_IR_VarId_alphaEqv(x_0, x_119, x_120);
return x_121;
}
default:
{
uint8 x_123; 
lean::dec(x_0);
x_123 = 0;
return x_123;
}
}
}
}
}
}
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Lean_IR_Expr_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Expr_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_Expr_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Expr_alphaEqv___boxed), 3, 0);
return x_0;
}
}
obj* l_Lean_IR_addVarRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_name_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Lean_NameMap_insert___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
}
}
obj* l_Lean_IR_addParamRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1 + 1);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1 + 1);
x_5 = l_Lean_IR_IRType_beq___main(x_3, x_4);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::box(0);
return x_9;
}
else
{
uint8 x_10; uint8 x_11; uint8 x_12; 
x_10 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_11 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_10 == 0)
{
if (x_11 == 0)
{
uint8 x_14; 
x_14 = 1;
x_12 = x_14;
goto lbl_13;
}
else
{
uint8 x_15; 
x_15 = 0;
x_12 = x_15;
goto lbl_13;
}
}
else
{
if (x_11 == 0)
{
uint8 x_16; 
x_16 = 0;
x_12 = x_16;
goto lbl_13;
}
else
{
uint8 x_17; 
x_17 = 1;
x_12 = x_17;
goto lbl_13;
}
}
lbl_13:
{
if (x_12 == 0)
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::box(0);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_28 = l_Lean_IR_addVarRename(x_0, x_22, x_25);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
obj* l_Lean_IR_addParamsRename___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
else
{
obj* x_6; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 1);
lean::inc(x_17);
lean::dec(x_2);
x_20 = l_Lean_IR_addParamRename(x_0, x_10, x_15);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; 
lean::dec(x_17);
lean::dec(x_12);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_0 = x_24;
x_1 = x_12;
x_2 = x_17;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_addParamsRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_addParamsRename___main(x_0, x_1, x_2);
return x_3;
}
}
uint8 l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = 0;
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; obj* x_20; obj* x_22; obj* x_25; obj* x_27; uint8 x_30; 
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_2, 1);
lean::inc(x_17);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_10, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_10, 1);
lean::inc(x_22);
lean::dec(x_10);
x_25 = lean::cnstr_get(x_12, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_12, 1);
lean::inc(x_27);
lean::dec(x_12);
x_30 = l_Lean_IR_CtorInfo_beq___main(x_20, x_25);
lean::dec(x_25);
lean::dec(x_20);
if (x_30 == 0)
{
uint8 x_38; 
lean::dec(x_0);
lean::dec(x_27);
lean::dec(x_14);
lean::dec(x_17);
lean::dec(x_22);
x_38 = 0;
return x_38;
}
else
{
uint8 x_40; 
lean::inc(x_0);
x_40 = l_Lean_IR_Fnbody_alphaEqv___main(x_0, x_22, x_27);
if (x_40 == 0)
{
uint8 x_44; 
lean::dec(x_0);
lean::dec(x_14);
lean::dec(x_17);
x_44 = 0;
return x_44;
}
else
{
x_1 = x_14;
x_2 = x_17;
goto _start;
}
}
}
else
{
uint8 x_51; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
lean::dec(x_10);
x_51 = 0;
return x_51;
}
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_2, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
uint8 x_59; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_52);
lean::dec(x_10);
x_59 = 0;
return x_59;
}
else
{
obj* x_60; obj* x_63; obj* x_66; obj* x_69; uint8 x_73; 
x_60 = lean::cnstr_get(x_1, 1);
lean::inc(x_60);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_2, 1);
lean::inc(x_63);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_10, 0);
lean::inc(x_66);
lean::dec(x_10);
x_69 = lean::cnstr_get(x_52, 0);
lean::inc(x_69);
lean::dec(x_52);
lean::inc(x_0);
x_73 = l_Lean_IR_Fnbody_alphaEqv___main(x_0, x_66, x_69);
if (x_73 == 0)
{
uint8 x_77; 
lean::dec(x_0);
lean::dec(x_60);
lean::dec(x_63);
x_77 = 0;
return x_77;
}
else
{
x_1 = x_60;
x_2 = x_63;
goto _start;
}
}
}
}
}
}
}
uint8 l_Lean_IR_Fnbody_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; uint8 x_13; obj* x_14; obj* x_16; uint8 x_19; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
lean::dec(x_2);
x_19 = l_Lean_IR_IRType_beq___main(x_3, x_13);
if (x_19 == 0)
{
uint8 x_27; 
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_14);
lean::dec(x_16);
x_27 = 0;
return x_27;
}
else
{
uint8 x_29; 
lean::inc(x_0);
x_29 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_6, x_14);
lean::dec(x_14);
lean::dec(x_6);
if (x_29 == 0)
{
uint8 x_37; 
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_16);
x_37 = 0;
return x_37;
}
else
{
obj* x_38; 
x_38 = l_Lean_IR_addVarRename(x_0, x_4, x_11);
x_0 = x_38;
x_1 = x_8;
x_2 = x_16;
goto _start;
}
}
}
case 12:
{
uint8 x_42; 
lean::dec(x_1);
lean::dec(x_0);
x_42 = 0;
return x_42;
}
default:
{
uint8 x_46; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_46 = 0;
return x_46;
}
}
}
case 1:
{
uint8 x_47; 
x_47 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_59; uint8 x_61; obj* x_62; obj* x_64; obj* x_68; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_1, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_1, 2);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_1, 3);
lean::inc(x_54);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_2, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_2, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
x_62 = lean::cnstr_get(x_2, 2);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_2, 3);
lean::inc(x_64);
lean::dec(x_2);
lean::inc(x_0);
x_68 = l_Lean_IR_addParamsRename___main(x_0, x_50, x_59);
if (lean::obj_tag(x_68) == 0)
{
uint8 x_76; 
lean::dec(x_0);
lean::dec(x_52);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_62);
lean::dec(x_48);
lean::dec(x_57);
x_76 = 0;
return x_76;
}
else
{
obj* x_77; uint8 x_80; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
lean::dec(x_68);
x_80 = l_Lean_IR_IRType_beq___main(x_47, x_61);
if (x_80 == 0)
{
uint8 x_89; 
lean::dec(x_0);
lean::dec(x_77);
lean::dec(x_52);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_62);
lean::dec(x_48);
lean::dec(x_57);
x_89 = 0;
return x_89;
}
else
{
uint8 x_90; 
x_90 = l_Lean_IR_Fnbody_alphaEqv___main(x_77, x_52, x_62);
if (x_90 == 0)
{
uint8 x_96; 
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_48);
lean::dec(x_57);
x_96 = 0;
return x_96;
}
else
{
obj* x_97; 
x_97 = l_Lean_IR_addVarRename(x_0, x_48, x_57);
x_0 = x_97;
x_1 = x_54;
x_2 = x_64;
goto _start;
}
}
}
}
case 12:
{
uint8 x_101; 
lean::dec(x_1);
lean::dec(x_0);
x_101 = 0;
return x_101;
}
default:
{
uint8 x_105; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_105 = 0;
return x_105;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_115; obj* x_117; obj* x_119; obj* x_121; uint8 x_125; 
x_106 = lean::cnstr_get(x_1, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_1, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_1, 2);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_1, 3);
lean::inc(x_112);
lean::dec(x_1);
x_115 = lean::cnstr_get(x_2, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_2, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_2, 2);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_2, 3);
lean::inc(x_121);
lean::dec(x_2);
lean::inc(x_0);
x_125 = l_Lean_IR_VarId_alphaEqv(x_0, x_106, x_115);
lean::dec(x_115);
lean::dec(x_106);
if (x_125 == 0)
{
uint8 x_135; 
lean::dec(x_119);
lean::dec(x_121);
lean::dec(x_108);
lean::dec(x_117);
lean::dec(x_110);
lean::dec(x_112);
lean::dec(x_0);
x_135 = 0;
return x_135;
}
else
{
uint8 x_136; 
x_136 = lean::nat_dec_eq(x_108, x_117);
lean::dec(x_117);
lean::dec(x_108);
if (x_136 == 0)
{
uint8 x_144; 
lean::dec(x_119);
lean::dec(x_121);
lean::dec(x_110);
lean::dec(x_112);
lean::dec(x_0);
x_144 = 0;
return x_144;
}
else
{
uint8 x_146; 
lean::inc(x_0);
x_146 = l_Lean_IR_VarId_alphaEqv(x_0, x_110, x_119);
lean::dec(x_119);
lean::dec(x_110);
if (x_146 == 0)
{
uint8 x_152; 
lean::dec(x_121);
lean::dec(x_112);
lean::dec(x_0);
x_152 = 0;
return x_152;
}
else
{
x_1 = x_112;
x_2 = x_121;
goto _start;
}
}
}
}
case 12:
{
uint8 x_156; 
lean::dec(x_1);
lean::dec(x_0);
x_156 = 0;
return x_156;
}
default:
{
uint8 x_160; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_160 = 0;
return x_160;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_170; obj* x_172; obj* x_174; obj* x_176; uint8 x_180; 
x_161 = lean::cnstr_get(x_1, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_1, 1);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_1, 2);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_1, 3);
lean::inc(x_167);
lean::dec(x_1);
x_170 = lean::cnstr_get(x_2, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_2, 1);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_2, 2);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_2, 3);
lean::inc(x_176);
lean::dec(x_2);
lean::inc(x_0);
x_180 = l_Lean_IR_VarId_alphaEqv(x_0, x_161, x_170);
lean::dec(x_170);
lean::dec(x_161);
if (x_180 == 0)
{
uint8 x_190; 
lean::dec(x_0);
lean::dec(x_163);
lean::dec(x_167);
lean::dec(x_176);
lean::dec(x_174);
lean::dec(x_172);
lean::dec(x_165);
x_190 = 0;
return x_190;
}
else
{
uint8 x_191; 
x_191 = lean::nat_dec_eq(x_163, x_172);
lean::dec(x_172);
lean::dec(x_163);
if (x_191 == 0)
{
uint8 x_199; 
lean::dec(x_0);
lean::dec(x_167);
lean::dec(x_176);
lean::dec(x_174);
lean::dec(x_165);
x_199 = 0;
return x_199;
}
else
{
uint8 x_201; 
lean::inc(x_0);
x_201 = l_Lean_IR_VarId_alphaEqv(x_0, x_165, x_174);
lean::dec(x_174);
lean::dec(x_165);
if (x_201 == 0)
{
uint8 x_207; 
lean::dec(x_0);
lean::dec(x_167);
lean::dec(x_176);
x_207 = 0;
return x_207;
}
else
{
x_1 = x_167;
x_2 = x_176;
goto _start;
}
}
}
}
case 12:
{
uint8 x_211; 
lean::dec(x_1);
lean::dec(x_0);
x_211 = 0;
return x_211;
}
default:
{
uint8 x_215; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_215 = 0;
return x_215;
}
}
}
case 4:
{
uint8 x_216; 
x_216 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_217; obj* x_219; obj* x_221; obj* x_223; obj* x_225; obj* x_228; obj* x_230; obj* x_232; obj* x_234; uint8 x_236; obj* x_237; uint8 x_241; 
x_217 = lean::cnstr_get(x_1, 0);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_1, 1);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_1, 2);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_1, 3);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_1, 4);
lean::inc(x_225);
lean::dec(x_1);
x_228 = lean::cnstr_get(x_2, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_2, 1);
lean::inc(x_230);
x_232 = lean::cnstr_get(x_2, 2);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_2, 3);
lean::inc(x_234);
x_236 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_237 = lean::cnstr_get(x_2, 4);
lean::inc(x_237);
lean::dec(x_2);
lean::inc(x_0);
x_241 = l_Lean_IR_VarId_alphaEqv(x_0, x_217, x_228);
lean::dec(x_228);
lean::dec(x_217);
if (x_241 == 0)
{
uint8 x_253; 
lean::dec(x_234);
lean::dec(x_237);
lean::dec(x_0);
lean::dec(x_232);
lean::dec(x_225);
lean::dec(x_219);
lean::dec(x_223);
lean::dec(x_221);
lean::dec(x_230);
x_253 = 0;
return x_253;
}
else
{
uint8 x_254; 
x_254 = lean::nat_dec_eq(x_219, x_230);
lean::dec(x_230);
lean::dec(x_219);
if (x_254 == 0)
{
uint8 x_264; 
lean::dec(x_234);
lean::dec(x_237);
lean::dec(x_0);
lean::dec(x_232);
lean::dec(x_225);
lean::dec(x_223);
lean::dec(x_221);
x_264 = 0;
return x_264;
}
else
{
uint8 x_265; 
x_265 = lean::nat_dec_eq(x_221, x_232);
lean::dec(x_232);
lean::dec(x_221);
if (x_265 == 0)
{
uint8 x_273; 
lean::dec(x_234);
lean::dec(x_237);
lean::dec(x_0);
lean::dec(x_225);
lean::dec(x_223);
x_273 = 0;
return x_273;
}
else
{
uint8 x_275; 
lean::inc(x_0);
x_275 = l_Lean_IR_VarId_alphaEqv(x_0, x_223, x_234);
lean::dec(x_234);
lean::dec(x_223);
if (x_275 == 0)
{
uint8 x_281; 
lean::dec(x_237);
lean::dec(x_0);
lean::dec(x_225);
x_281 = 0;
return x_281;
}
else
{
uint8 x_282; 
x_282 = l_Lean_IR_IRType_beq___main(x_216, x_236);
if (x_282 == 0)
{
uint8 x_286; 
lean::dec(x_237);
lean::dec(x_0);
lean::dec(x_225);
x_286 = 0;
return x_286;
}
else
{
x_1 = x_225;
x_2 = x_237;
goto _start;
}
}
}
}
}
}
case 12:
{
uint8 x_290; 
lean::dec(x_1);
lean::dec(x_0);
x_290 = 0;
return x_290;
}
default:
{
uint8 x_294; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_294 = 0;
return x_294;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_295; obj* x_297; obj* x_299; obj* x_302; obj* x_304; obj* x_306; uint8 x_310; 
x_295 = lean::cnstr_get(x_1, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_1, 1);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_1, 2);
lean::inc(x_299);
lean::dec(x_1);
x_302 = lean::cnstr_get(x_2, 0);
lean::inc(x_302);
x_304 = lean::cnstr_get(x_2, 1);
lean::inc(x_304);
x_306 = lean::cnstr_get(x_2, 2);
lean::inc(x_306);
lean::dec(x_2);
lean::inc(x_0);
x_310 = l_Lean_IR_VarId_alphaEqv(x_0, x_295, x_302);
lean::dec(x_302);
lean::dec(x_295);
if (x_310 == 0)
{
uint8 x_318; 
lean::dec(x_306);
lean::dec(x_304);
lean::dec(x_297);
lean::dec(x_299);
lean::dec(x_0);
x_318 = 0;
return x_318;
}
else
{
uint8 x_319; 
x_319 = lean::nat_dec_eq(x_297, x_304);
lean::dec(x_304);
lean::dec(x_297);
if (x_319 == 0)
{
uint8 x_325; 
lean::dec(x_306);
lean::dec(x_299);
lean::dec(x_0);
x_325 = 0;
return x_325;
}
else
{
x_1 = x_299;
x_2 = x_306;
goto _start;
}
}
}
case 12:
{
uint8 x_329; 
lean::dec(x_1);
lean::dec(x_0);
x_329 = 0;
return x_329;
}
default:
{
uint8 x_333; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_333 = 0;
return x_333;
}
}
}
case 6:
{
uint8 x_334; 
x_334 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_335; obj* x_337; obj* x_339; obj* x_342; obj* x_344; uint8 x_346; obj* x_347; uint8 x_351; 
x_335 = lean::cnstr_get(x_1, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_1, 1);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_1, 2);
lean::inc(x_339);
lean::dec(x_1);
x_342 = lean::cnstr_get(x_2, 0);
lean::inc(x_342);
x_344 = lean::cnstr_get(x_2, 1);
lean::inc(x_344);
x_346 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_347 = lean::cnstr_get(x_2, 2);
lean::inc(x_347);
lean::dec(x_2);
lean::inc(x_0);
x_351 = l_Lean_IR_VarId_alphaEqv(x_0, x_335, x_342);
lean::dec(x_342);
lean::dec(x_335);
if (x_351 == 0)
{
uint8 x_359; 
lean::dec(x_0);
lean::dec(x_337);
lean::dec(x_339);
lean::dec(x_344);
lean::dec(x_347);
x_359 = 0;
return x_359;
}
else
{
uint8 x_360; 
x_360 = lean::nat_dec_eq(x_337, x_344);
lean::dec(x_344);
lean::dec(x_337);
if (x_360 == 0)
{
uint8 x_366; 
lean::dec(x_0);
lean::dec(x_339);
lean::dec(x_347);
x_366 = 0;
return x_366;
}
else
{
if (x_334 == 0)
{
if (x_346 == 0)
{
x_1 = x_339;
x_2 = x_347;
goto _start;
}
else
{
uint8 x_371; 
lean::dec(x_0);
lean::dec(x_339);
lean::dec(x_347);
x_371 = 0;
return x_371;
}
}
else
{
if (x_346 == 0)
{
uint8 x_375; 
lean::dec(x_0);
lean::dec(x_339);
lean::dec(x_347);
x_375 = 0;
return x_375;
}
else
{
x_1 = x_339;
x_2 = x_347;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_379; 
lean::dec(x_1);
lean::dec(x_0);
x_379 = 0;
return x_379;
}
default:
{
uint8 x_383; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_383 = 0;
return x_383;
}
}
}
case 7:
{
uint8 x_384; 
x_384 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_385; obj* x_387; obj* x_389; obj* x_392; obj* x_394; uint8 x_396; obj* x_397; uint8 x_401; 
x_385 = lean::cnstr_get(x_1, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_1, 1);
lean::inc(x_387);
x_389 = lean::cnstr_get(x_1, 2);
lean::inc(x_389);
lean::dec(x_1);
x_392 = lean::cnstr_get(x_2, 0);
lean::inc(x_392);
x_394 = lean::cnstr_get(x_2, 1);
lean::inc(x_394);
x_396 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_397 = lean::cnstr_get(x_2, 2);
lean::inc(x_397);
lean::dec(x_2);
lean::inc(x_0);
x_401 = l_Lean_IR_VarId_alphaEqv(x_0, x_385, x_392);
lean::dec(x_392);
lean::dec(x_385);
if (x_401 == 0)
{
uint8 x_409; 
lean::dec(x_394);
lean::dec(x_387);
lean::dec(x_389);
lean::dec(x_397);
lean::dec(x_0);
x_409 = 0;
return x_409;
}
else
{
uint8 x_410; 
x_410 = lean::nat_dec_eq(x_387, x_394);
lean::dec(x_394);
lean::dec(x_387);
if (x_410 == 0)
{
uint8 x_416; 
lean::dec(x_389);
lean::dec(x_397);
lean::dec(x_0);
x_416 = 0;
return x_416;
}
else
{
if (x_384 == 0)
{
if (x_396 == 0)
{
x_1 = x_389;
x_2 = x_397;
goto _start;
}
else
{
uint8 x_421; 
lean::dec(x_389);
lean::dec(x_397);
lean::dec(x_0);
x_421 = 0;
return x_421;
}
}
else
{
if (x_396 == 0)
{
uint8 x_425; 
lean::dec(x_389);
lean::dec(x_397);
lean::dec(x_0);
x_425 = 0;
return x_425;
}
else
{
x_1 = x_389;
x_2 = x_397;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_429; 
lean::dec(x_1);
lean::dec(x_0);
x_429 = 0;
return x_429;
}
default:
{
uint8 x_433; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_433 = 0;
return x_433;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_434; obj* x_436; obj* x_439; obj* x_441; uint8 x_444; 
x_434 = lean::cnstr_get(x_1, 0);
lean::inc(x_434);
x_436 = lean::cnstr_get(x_1, 1);
lean::inc(x_436);
lean::dec(x_1);
x_439 = lean::cnstr_get(x_2, 0);
lean::inc(x_439);
x_441 = lean::cnstr_get(x_2, 1);
lean::inc(x_441);
lean::dec(x_2);
x_444 = l_Lean_KVMap_eqv(x_434, x_439);
if (x_444 == 0)
{
uint8 x_448; 
lean::dec(x_0);
lean::dec(x_441);
lean::dec(x_436);
x_448 = 0;
return x_448;
}
else
{
x_1 = x_436;
x_2 = x_441;
goto _start;
}
}
case 12:
{
uint8 x_452; 
lean::dec(x_1);
lean::dec(x_0);
x_452 = 0;
return x_452;
}
default:
{
uint8 x_456; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_456 = 0;
return x_456;
}
}
}
case 9:
{
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_457; obj* x_459; obj* x_461; obj* x_464; obj* x_466; obj* x_468; uint8 x_471; 
x_457 = lean::cnstr_get(x_1, 0);
lean::inc(x_457);
x_459 = lean::cnstr_get(x_1, 1);
lean::inc(x_459);
x_461 = lean::cnstr_get(x_1, 2);
lean::inc(x_461);
lean::dec(x_1);
x_464 = lean::cnstr_get(x_2, 0);
lean::inc(x_464);
x_466 = lean::cnstr_get(x_2, 1);
lean::inc(x_466);
x_468 = lean::cnstr_get(x_2, 2);
lean::inc(x_468);
lean::dec(x_2);
x_471 = lean_name_dec_eq(x_457, x_464);
lean::dec(x_464);
lean::dec(x_457);
if (x_471 == 0)
{
uint8 x_479; 
lean::dec(x_0);
lean::dec(x_459);
lean::dec(x_461);
lean::dec(x_466);
lean::dec(x_468);
x_479 = 0;
return x_479;
}
else
{
uint8 x_481; 
lean::inc(x_0);
x_481 = l_Lean_IR_VarId_alphaEqv(x_0, x_459, x_466);
lean::dec(x_466);
lean::dec(x_459);
if (x_481 == 0)
{
uint8 x_487; 
lean::dec(x_0);
lean::dec(x_461);
lean::dec(x_468);
x_487 = 0;
return x_487;
}
else
{
uint8 x_488; 
x_488 = l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1(x_0, x_461, x_468);
return x_488;
}
}
}
case 12:
{
uint8 x_491; 
lean::dec(x_1);
lean::dec(x_0);
x_491 = 0;
return x_491;
}
default:
{
uint8 x_495; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_495 = 0;
return x_495;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_496; obj* x_499; uint8 x_502; 
x_496 = lean::cnstr_get(x_1, 0);
lean::inc(x_496);
lean::dec(x_1);
x_499 = lean::cnstr_get(x_2, 0);
lean::inc(x_499);
lean::dec(x_2);
x_502 = l_Lean_IR_VarId_alphaEqv(x_0, x_496, x_499);
lean::dec(x_499);
lean::dec(x_496);
return x_502;
}
case 12:
{
uint8 x_507; 
lean::dec(x_1);
lean::dec(x_0);
x_507 = 0;
return x_507;
}
default:
{
uint8 x_511; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_511 = 0;
return x_511;
}
}
}
case 11:
{
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_512; obj* x_514; obj* x_517; obj* x_519; uint8 x_522; 
x_512 = lean::cnstr_get(x_1, 0);
lean::inc(x_512);
x_514 = lean::cnstr_get(x_1, 1);
lean::inc(x_514);
lean::dec(x_1);
x_517 = lean::cnstr_get(x_2, 0);
lean::inc(x_517);
x_519 = lean::cnstr_get(x_2, 1);
lean::inc(x_519);
lean::dec(x_2);
x_522 = lean_name_dec_eq(x_512, x_517);
lean::dec(x_517);
lean::dec(x_512);
if (x_522 == 0)
{
uint8 x_528; 
lean::dec(x_519);
lean::dec(x_514);
lean::dec(x_0);
x_528 = 0;
return x_528;
}
else
{
uint8 x_529; 
x_529 = l_Lean_IR_args_alphaEqv___main(x_0, x_514, x_519);
lean::dec(x_519);
lean::dec(x_514);
return x_529;
}
}
case 12:
{
uint8 x_534; 
lean::dec(x_1);
lean::dec(x_0);
x_534 = 0;
return x_534;
}
default:
{
uint8 x_538; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_538 = 0;
return x_538;
}
}
}
default:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 12:
{
uint8 x_540; 
x_540 = 1;
return x_540;
}
default:
{
uint8 x_542; 
lean::dec(x_2);
x_542 = 0;
return x_542;
}
}
}
}
}
}
obj* l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_IR_Fnbody_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Fnbody_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_Fnbody_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Fnbody_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Fnbody_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Fnbody_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_Fnbody_beq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::box(0);
x_3 = l_Lean_IR_Fnbody_alphaEqv___main(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_IR_Fnbody_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Fnbody_beq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_Fnbody_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Fnbody_beq___boxed), 2, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_1__skip___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_1__skip(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_1__skip___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_1__skip___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_1__skip___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_1__skip___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_1__skip(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_2__collectVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_NameSet_contains(x_1, x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Lean_NameSet_insert(x_2, x_0);
return x_4;
}
else
{
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_3__withBv(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_NameSet_insert(x_2, x_0);
x_5 = lean::apply_2(x_1, x_4, x_3);
return x_5;
}
}
obj* l_List_foldl___main___at_Lean_IR_insertParams___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_Lean_NameSet_insert(x_0, x_7);
x_0 = x_10;
x_1 = x_4;
goto _start;
}
}
}
obj* l_Lean_IR_insertParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_Lean_IR_insertParams___spec__1(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_4__withParams(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_List_foldl___main___at_Lean_IR_insertParams___spec__1(x_2, x_0);
x_5 = lean::apply_2(x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_5__seq(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::apply_2(x_1, x_2, x_5);
return x_6;
}
}
obj* _init_l_Lean_IR_HasAndthen() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_5__seq), 4, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_6__collectArg___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; uint8 x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_NameSet_contains(x_1, x_3);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_Lean_NameSet_insert(x_2, x_3);
return x_7;
}
else
{
lean::dec(x_3);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_6__collectArg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_6__collectArg___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArgs___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
lean::inc(x_1);
x_10 = l___private_init_lean_compiler_ir_6__collectArg___main(x_4, x_1, x_2);
x_0 = x_6;
x_2 = x_10;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_7__collectArgs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_8__collectExpr___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_3, x_1, x_2);
return x_6;
}
case 2:
{
obj* x_7; obj* x_9; uint8 x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_Lean_NameSet_contains(x_1, x_7);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_Lean_NameSet_insert(x_2, x_7);
x_15 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_9, x_1, x_14);
return x_15;
}
else
{
obj* x_17; 
lean::dec(x_7);
x_17 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_9, x_1, x_2);
return x_17;
}
}
case 3:
{
obj* x_18; uint8 x_21; 
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_Lean_NameSet_contains(x_1, x_18);
if (x_21 == 0)
{
obj* x_22; 
x_22 = l_Lean_NameSet_insert(x_2, x_18);
return x_22;
}
else
{
lean::dec(x_18);
return x_2;
}
}
case 4:
{
obj* x_24; uint8 x_27; 
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l_Lean_NameSet_contains(x_1, x_24);
if (x_27 == 0)
{
obj* x_28; 
x_28 = l_Lean_NameSet_insert(x_2, x_24);
return x_28;
}
else
{
lean::dec(x_24);
return x_2;
}
}
case 5:
{
obj* x_30; uint8 x_33; 
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_Lean_NameSet_contains(x_1, x_30);
if (x_33 == 0)
{
obj* x_34; 
x_34 = l_Lean_NameSet_insert(x_2, x_30);
return x_34;
}
else
{
lean::dec(x_30);
return x_2;
}
}
case 6:
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_0, 1);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_36, x_1, x_2);
return x_39;
}
case 7:
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_0, 1);
lean::inc(x_40);
lean::dec(x_0);
x_43 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_40, x_1, x_2);
return x_43;
}
case 8:
{
obj* x_44; obj* x_46; uint8 x_50; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
lean::dec(x_0);
lean::inc(x_1);
x_50 = l_Lean_NameSet_contains(x_1, x_44);
if (x_50 == 0)
{
obj* x_51; obj* x_52; 
x_51 = l_Lean_NameSet_insert(x_2, x_44);
x_52 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_46, x_1, x_51);
return x_52;
}
else
{
obj* x_54; 
lean::dec(x_44);
x_54 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_46, x_1, x_2);
return x_54;
}
}
case 11:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
default:
{
obj* x_57; uint8 x_60; 
x_57 = lean::cnstr_get(x_0, 0);
lean::inc(x_57);
lean::dec(x_0);
x_60 = l_Lean_NameSet_contains(x_1, x_57);
if (x_60 == 0)
{
obj* x_61; 
x_61 = l_Lean_NameSet_insert(x_2, x_57);
return x_61;
}
else
{
lean::dec(x_57);
return x_2;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_8__collectExpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_8__collectExpr___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_9__collectAlts___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_11; obj* x_16; 
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_11, x_2, x_3);
x_1 = x_8;
x_3 = x_16;
goto _start;
}
else
{
obj* x_18; obj* x_21; obj* x_26; 
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_0);
x_26 = lean::apply_3(x_0, x_21, x_2, x_3);
x_1 = x_18;
x_3 = x_26;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_9__collectAlts(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_9__collectAlts___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_10__collectFnBody___main), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_10__collectFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
x_11 = l___private_init_lean_compiler_ir_8__collectExpr___main(x_5, x_1, x_2);
x_12 = l_Lean_NameSet_insert(x_1, x_3);
x_0 = x_7;
x_1 = x_12;
x_2 = x_11;
goto _start;
}
case 1:
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_24; obj* x_25; obj* x_26; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 2);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 3);
lean::inc(x_20);
lean::dec(x_0);
lean::inc(x_1);
x_24 = l_List_foldl___main___at_Lean_IR_insertParams___spec__1(x_1, x_16);
x_25 = l___private_init_lean_compiler_ir_10__collectFnBody___main(x_18, x_24, x_2);
x_26 = l_Lean_NameSet_insert(x_1, x_14);
x_0 = x_20;
x_1 = x_26;
x_2 = x_25;
goto _start;
}
case 2:
{
obj* x_28; obj* x_30; obj* x_32; uint8 x_36; uint8 x_38; 
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 2);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 3);
lean::inc(x_32);
lean::dec(x_0);
lean::inc(x_1);
x_36 = l_Lean_NameSet_contains(x_1, x_28);
lean::inc(x_1);
x_38 = l_Lean_NameSet_contains(x_1, x_30);
if (x_36 == 0)
{
obj* x_39; 
x_39 = l_Lean_NameSet_insert(x_2, x_28);
if (x_38 == 0)
{
obj* x_40; 
x_40 = l_Lean_NameSet_insert(x_39, x_30);
x_0 = x_32;
x_2 = x_40;
goto _start;
}
else
{
lean::dec(x_30);
x_0 = x_32;
x_2 = x_39;
goto _start;
}
}
else
{
lean::dec(x_28);
if (x_38 == 0)
{
obj* x_45; 
x_45 = l_Lean_NameSet_insert(x_2, x_30);
x_0 = x_32;
x_2 = x_45;
goto _start;
}
else
{
lean::dec(x_30);
x_0 = x_32;
goto _start;
}
}
}
case 3:
{
obj* x_49; obj* x_51; obj* x_53; uint8 x_57; uint8 x_59; 
x_49 = lean::cnstr_get(x_0, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_0, 2);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_0, 3);
lean::inc(x_53);
lean::dec(x_0);
lean::inc(x_1);
x_57 = l_Lean_NameSet_contains(x_1, x_49);
lean::inc(x_1);
x_59 = l_Lean_NameSet_contains(x_1, x_51);
if (x_57 == 0)
{
obj* x_60; 
x_60 = l_Lean_NameSet_insert(x_2, x_49);
if (x_59 == 0)
{
obj* x_61; 
x_61 = l_Lean_NameSet_insert(x_60, x_51);
x_0 = x_53;
x_2 = x_61;
goto _start;
}
else
{
lean::dec(x_51);
x_0 = x_53;
x_2 = x_60;
goto _start;
}
}
else
{
lean::dec(x_49);
if (x_59 == 0)
{
obj* x_66; 
x_66 = l_Lean_NameSet_insert(x_2, x_51);
x_0 = x_53;
x_2 = x_66;
goto _start;
}
else
{
lean::dec(x_51);
x_0 = x_53;
goto _start;
}
}
}
case 4:
{
obj* x_70; obj* x_72; obj* x_74; uint8 x_78; uint8 x_80; 
x_70 = lean::cnstr_get(x_0, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_0, 3);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_0, 4);
lean::inc(x_74);
lean::dec(x_0);
lean::inc(x_1);
x_78 = l_Lean_NameSet_contains(x_1, x_70);
lean::inc(x_1);
x_80 = l_Lean_NameSet_contains(x_1, x_72);
if (x_78 == 0)
{
obj* x_81; 
x_81 = l_Lean_NameSet_insert(x_2, x_70);
if (x_80 == 0)
{
obj* x_82; 
x_82 = l_Lean_NameSet_insert(x_81, x_72);
x_0 = x_74;
x_2 = x_82;
goto _start;
}
else
{
lean::dec(x_72);
x_0 = x_74;
x_2 = x_81;
goto _start;
}
}
else
{
lean::dec(x_70);
if (x_80 == 0)
{
obj* x_87; 
x_87 = l_Lean_NameSet_insert(x_2, x_72);
x_0 = x_74;
x_2 = x_87;
goto _start;
}
else
{
lean::dec(x_72);
x_0 = x_74;
goto _start;
}
}
}
case 8:
{
obj* x_91; 
x_91 = lean::cnstr_get(x_0, 1);
lean::inc(x_91);
lean::dec(x_0);
x_0 = x_91;
goto _start;
}
case 9:
{
obj* x_95; obj* x_97; uint8 x_101; 
x_95 = lean::cnstr_get(x_0, 1);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_0, 2);
lean::inc(x_97);
lean::dec(x_0);
lean::inc(x_1);
x_101 = l_Lean_NameSet_contains(x_1, x_95);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = l_Lean_NameSet_insert(x_2, x_95);
x_103 = l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1;
x_104 = l___private_init_lean_compiler_ir_9__collectAlts___main(x_103, x_97, x_1, x_102);
return x_104;
}
else
{
obj* x_106; obj* x_107; 
lean::dec(x_95);
x_106 = l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1;
x_107 = l___private_init_lean_compiler_ir_9__collectAlts___main(x_106, x_97, x_1, x_2);
return x_107;
}
}
case 10:
{
obj* x_108; uint8 x_111; 
x_108 = lean::cnstr_get(x_0, 0);
lean::inc(x_108);
lean::dec(x_0);
x_111 = l_Lean_NameSet_contains(x_1, x_108);
if (x_111 == 0)
{
obj* x_112; 
x_112 = l_Lean_NameSet_insert(x_2, x_108);
return x_112;
}
else
{
lean::dec(x_108);
return x_2;
}
}
case 11:
{
obj* x_114; obj* x_116; uint8 x_120; 
x_114 = lean::cnstr_get(x_0, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_0, 1);
lean::inc(x_116);
lean::dec(x_0);
lean::inc(x_1);
x_120 = l_Lean_NameSet_contains(x_1, x_114);
if (x_120 == 0)
{
obj* x_121; obj* x_122; 
x_121 = l_Lean_NameSet_insert(x_2, x_114);
x_122 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_116, x_1, x_121);
return x_122;
}
else
{
obj* x_124; 
lean::dec(x_114);
x_124 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_116, x_1, x_2);
return x_124;
}
}
case 12:
{
lean::dec(x_1);
return x_2;
}
default:
{
obj* x_126; obj* x_128; uint8 x_132; 
x_126 = lean::cnstr_get(x_0, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_0, 2);
lean::inc(x_128);
lean::dec(x_0);
lean::inc(x_1);
x_132 = l_Lean_NameSet_contains(x_1, x_126);
if (x_132 == 0)
{
obj* x_133; 
x_133 = l_Lean_NameSet_insert(x_2, x_126);
x_0 = x_128;
x_2 = x_133;
goto _start;
}
else
{
lean::dec(x_126);
x_0 = x_128;
goto _start;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_10__collectFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_10__collectFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_freeVars(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_10__collectFnBody___main(x_0, x_1, x_1);
return x_2;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_kvmap(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
 l_Lean_IR_MData_empty = _init_l_Lean_IR_MData_empty();
lean::mark_persistent(l_Lean_IR_MData_empty);
 l_Lean_IR_MData_HasEmptyc = _init_l_Lean_IR_MData_HasEmptyc();
lean::mark_persistent(l_Lean_IR_MData_HasEmptyc);
 l_Lean_IR_IRType_HasBeq = _init_l_Lean_IR_IRType_HasBeq();
lean::mark_persistent(l_Lean_IR_IRType_HasBeq);
 l_Lean_IR_Litval_HasBeq = _init_l_Lean_IR_Litval_HasBeq();
lean::mark_persistent(l_Lean_IR_Litval_HasBeq);
 l_Lean_IR_CtorInfo_HasBeq = _init_l_Lean_IR_CtorInfo_HasBeq();
lean::mark_persistent(l_Lean_IR_CtorInfo_HasBeq);
 l_Lean_IR_VarId_hasAeqv = _init_l_Lean_IR_VarId_hasAeqv();
lean::mark_persistent(l_Lean_IR_VarId_hasAeqv);
 l_Lean_IR_Arg_hasAeqv = _init_l_Lean_IR_Arg_hasAeqv();
lean::mark_persistent(l_Lean_IR_Arg_hasAeqv);
 l_Lean_IR_args_hasAeqv = _init_l_Lean_IR_args_hasAeqv();
lean::mark_persistent(l_Lean_IR_args_hasAeqv);
 l_Lean_IR_Expr_hasAeqv = _init_l_Lean_IR_Expr_hasAeqv();
lean::mark_persistent(l_Lean_IR_Expr_hasAeqv);
 l_Lean_IR_Fnbody_HasBeq = _init_l_Lean_IR_Fnbody_HasBeq();
lean::mark_persistent(l_Lean_IR_Fnbody_HasBeq);
 l_Lean_IR_HasAndthen = _init_l_Lean_IR_HasAndthen();
lean::mark_persistent(l_Lean_IR_HasAndthen);
 l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1 = _init_l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_10__collectFnBody___main___closed__1);
return w;
}
