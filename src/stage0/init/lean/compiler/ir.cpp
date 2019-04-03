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
extern obj* l_Lean_NameMap_contains___rarg___closed__1;
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_9__collectFnBody___main___spec__2(obj*, obj*, obj*);
uint8 l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_Litval_beq___main___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
uint8 l_Lean_IR_IRType_beq(uint8, uint8);
uint8 l_Lean_IR_Arg_alphaEqv(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_addParamRename(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_HasBeq;
obj* l___private_init_lean_compiler_ir_8__collectExpr___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_3__withBv(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_5__Seq(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_insertParams(obj*, obj*);
uint8 l_Lean_IR_Fnbody_beq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_8__collectExpr(obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_beq(obj*, obj*);
obj* l_Lean_IR_Fnbody_HasBeq;
obj* l___private_init_lean_compiler_ir_9__collectFnBody___main(obj*, obj*, obj*);
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
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_9__collectFnBody___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_args_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_HasBeq;
obj* l_Lean_IR_Expr_isPure___boxed(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_Litval_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArgs___main(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___main___boxed(obj*);
obj* l_Lean_IR_addVarRename(obj*, obj*, obj*);
obj* l_Lean_IR_Fnbody_isPure___boxed(obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_Arg_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Fnbody_alphaEqv___main(obj*, obj*, obj*);
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
obj* l___private_init_lean_compiler_ir_9__collectFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg___boxed(obj*);
obj* l_Lean_IR_Fnbody_beq___boxed(obj*, obj*);
uint8 l_Lean_IR_Fnbody_isPure(obj*);
obj* l___private_init_lean_compiler_ir_4__withParams(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___boxed(obj*, obj*);
obj* l_Lean_IR_MData_empty;
obj* l_Lean_IR_IRType_beq___main___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg(obj*);
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
uint8 l_Lean_IR_VarId_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_Lean_NameMap_contains___rarg___closed__1;
lean::inc(x_1);
x_5 = l_RBNode_find___main___rarg(x_3, lean::box(0), x_0, x_1);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = lean_name_dec_eq(x_1, x_2);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_9; uint8 x_12; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_12 = lean_name_dec_eq(x_9, x_2);
lean::dec(x_9);
return x_12;
}
}
}
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_VarId_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
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
obj* x_3; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_2, 0);
x_7 = l_Lean_IR_VarId_alphaEqv(x_0, x_3, x_6);
return x_7;
}
else
{
uint8 x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = 0;
return x_10;
}
}
else
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
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
uint8 x_8; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_14; obj* x_15; uint8 x_17; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_17 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_9, x_14);
if (x_17 == 0)
{
uint8 x_20; 
lean::dec(x_0);
lean::dec(x_11);
x_20 = 0;
return x_20;
}
else
{
x_1 = x_11;
x_2 = x_15;
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
obj* x_3; obj* x_5; obj* x_8; obj* x_10; uint8 x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
x_13 = l_Lean_IR_CtorInfo_beq___main(x_3, x_8);
lean::dec(x_8);
lean::dec(x_3);
if (x_13 == 0)
{
uint8 x_19; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_0);
x_19 = 0;
return x_19;
}
else
{
uint8 x_20; 
x_20 = l_Lean_IR_args_alphaEqv___main(x_0, x_5, x_10);
lean::dec(x_10);
return x_20;
}
}
default:
{
uint8 x_25; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_25 = 0;
return x_25;
}
}
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_26; obj* x_29; uint8 x_32; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
lean::dec(x_1);
x_29 = lean::cnstr_get(x_2, 0);
lean::inc(x_29);
lean::dec(x_2);
x_32 = l_Lean_IR_VarId_alphaEqv(x_0, x_26, x_29);
lean::dec(x_29);
return x_32;
}
default:
{
uint8 x_37; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_37 = 0;
return x_37;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_38; obj* x_40; obj* x_42; obj* x_45; obj* x_47; obj* x_49; uint8 x_53; 
x_38 = lean::cnstr_get(x_1, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 2);
lean::inc(x_42);
lean::dec(x_1);
x_45 = lean::cnstr_get(x_2, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_2, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 2);
lean::inc(x_49);
lean::dec(x_2);
lean::inc(x_0);
x_53 = l_Lean_IR_VarId_alphaEqv(x_0, x_38, x_45);
lean::dec(x_45);
if (x_53 == 0)
{
uint8 x_60; 
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_47);
lean::dec(x_40);
lean::dec(x_42);
x_60 = 0;
return x_60;
}
else
{
uint8 x_61; 
x_61 = l_Lean_IR_CtorInfo_beq___main(x_40, x_47);
lean::dec(x_47);
lean::dec(x_40);
if (x_61 == 0)
{
uint8 x_67; 
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_42);
x_67 = 0;
return x_67;
}
else
{
uint8 x_68; 
x_68 = l_Lean_IR_args_alphaEqv___main(x_0, x_42, x_49);
lean::dec(x_49);
return x_68;
}
}
}
default:
{
uint8 x_73; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_73 = 0;
return x_73;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_74; obj* x_76; obj* x_79; obj* x_81; uint8 x_84; 
x_74 = lean::cnstr_get(x_1, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_1, 1);
lean::inc(x_76);
lean::dec(x_1);
x_79 = lean::cnstr_get(x_2, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_2, 1);
lean::inc(x_81);
lean::dec(x_2);
x_84 = lean::nat_dec_eq(x_74, x_79);
lean::dec(x_79);
lean::dec(x_74);
if (x_84 == 0)
{
uint8 x_90; 
lean::dec(x_81);
lean::dec(x_76);
lean::dec(x_0);
x_90 = 0;
return x_90;
}
else
{
uint8 x_91; 
x_91 = l_Lean_IR_VarId_alphaEqv(x_0, x_76, x_81);
lean::dec(x_81);
return x_91;
}
}
default:
{
uint8 x_96; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_96 = 0;
return x_96;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_97; obj* x_99; obj* x_102; obj* x_104; uint8 x_107; 
x_97 = lean::cnstr_get(x_1, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_1, 1);
lean::inc(x_99);
lean::dec(x_1);
x_102 = lean::cnstr_get(x_2, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_2, 1);
lean::inc(x_104);
lean::dec(x_2);
x_107 = lean::nat_dec_eq(x_97, x_102);
lean::dec(x_102);
lean::dec(x_97);
if (x_107 == 0)
{
uint8 x_113; 
lean::dec(x_99);
lean::dec(x_104);
lean::dec(x_0);
x_113 = 0;
return x_113;
}
else
{
uint8 x_114; 
x_114 = l_Lean_IR_VarId_alphaEqv(x_0, x_99, x_104);
lean::dec(x_104);
return x_114;
}
}
default:
{
uint8 x_119; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_119 = 0;
return x_119;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_120; obj* x_122; obj* x_125; obj* x_127; uint8 x_130; 
x_120 = lean::cnstr_get(x_1, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_1, 1);
lean::inc(x_122);
lean::dec(x_1);
x_125 = lean::cnstr_get(x_2, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_2, 1);
lean::inc(x_127);
lean::dec(x_2);
x_130 = lean::nat_dec_eq(x_120, x_125);
lean::dec(x_125);
lean::dec(x_120);
if (x_130 == 0)
{
uint8 x_136; 
lean::dec(x_0);
lean::dec(x_122);
lean::dec(x_127);
x_136 = 0;
return x_136;
}
else
{
uint8 x_137; 
x_137 = l_Lean_IR_VarId_alphaEqv(x_0, x_122, x_127);
lean::dec(x_127);
return x_137;
}
}
default:
{
uint8 x_142; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_142 = 0;
return x_142;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_143; obj* x_145; obj* x_148; obj* x_150; uint8 x_153; 
x_143 = lean::cnstr_get(x_1, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_1, 1);
lean::inc(x_145);
lean::dec(x_1);
x_148 = lean::cnstr_get(x_2, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_2, 1);
lean::inc(x_150);
lean::dec(x_2);
x_153 = lean_name_dec_eq(x_143, x_148);
lean::dec(x_148);
lean::dec(x_143);
if (x_153 == 0)
{
uint8 x_159; 
lean::dec(x_0);
lean::dec(x_150);
lean::dec(x_145);
x_159 = 0;
return x_159;
}
else
{
uint8 x_160; 
x_160 = l_Lean_IR_args_alphaEqv___main(x_0, x_145, x_150);
lean::dec(x_150);
return x_160;
}
}
default:
{
uint8 x_165; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_165 = 0;
return x_165;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_166; obj* x_169; obj* x_171; uint8 x_174; 
x_166 = lean::cnstr_get(x_1, 0);
lean::inc(x_166);
lean::dec(x_1);
x_169 = lean::cnstr_get(x_2, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_2, 1);
lean::inc(x_171);
lean::dec(x_2);
x_174 = lean_name_dec_eq(x_166, x_169);
lean::dec(x_169);
lean::dec(x_166);
if (x_174 == 0)
{
uint8 x_179; 
lean::dec(x_171);
lean::dec(x_0);
x_179 = 0;
return x_179;
}
else
{
uint8 x_181; 
lean::inc(x_171);
x_181 = l_Lean_IR_args_alphaEqv___main(x_0, x_171, x_171);
lean::dec(x_171);
return x_181;
}
}
default:
{
uint8 x_186; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_186 = 0;
return x_186;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_187; obj* x_189; obj* x_192; obj* x_194; uint8 x_198; 
x_187 = lean::cnstr_get(x_1, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_1, 1);
lean::inc(x_189);
lean::dec(x_1);
x_192 = lean::cnstr_get(x_2, 0);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_2, 1);
lean::inc(x_194);
lean::dec(x_2);
lean::inc(x_0);
x_198 = l_Lean_IR_VarId_alphaEqv(x_0, x_187, x_192);
lean::dec(x_192);
if (x_198 == 0)
{
uint8 x_203; 
lean::dec(x_0);
lean::dec(x_194);
lean::dec(x_189);
x_203 = 0;
return x_203;
}
else
{
uint8 x_204; 
x_204 = l_Lean_IR_args_alphaEqv___main(x_0, x_189, x_194);
lean::dec(x_194);
return x_204;
}
}
default:
{
uint8 x_209; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_209 = 0;
return x_209;
}
}
}
case 9:
{
uint8 x_210; 
x_210 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_211; uint8 x_214; obj* x_215; uint8 x_218; 
x_211 = lean::cnstr_get(x_1, 0);
lean::inc(x_211);
lean::dec(x_1);
x_214 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_215 = lean::cnstr_get(x_2, 0);
lean::inc(x_215);
lean::dec(x_2);
x_218 = l_Lean_IR_IRType_beq___main(x_210, x_214);
if (x_218 == 0)
{
uint8 x_222; 
lean::dec(x_0);
lean::dec(x_211);
lean::dec(x_215);
x_222 = 0;
return x_222;
}
else
{
uint8 x_223; 
x_223 = l_Lean_IR_VarId_alphaEqv(x_0, x_211, x_215);
lean::dec(x_215);
return x_223;
}
}
default:
{
uint8 x_228; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_228 = 0;
return x_228;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_229; obj* x_232; uint8 x_235; 
x_229 = lean::cnstr_get(x_1, 0);
lean::inc(x_229);
lean::dec(x_1);
x_232 = lean::cnstr_get(x_2, 0);
lean::inc(x_232);
lean::dec(x_2);
x_235 = l_Lean_IR_VarId_alphaEqv(x_0, x_229, x_232);
lean::dec(x_232);
return x_235;
}
default:
{
uint8 x_240; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_240 = 0;
return x_240;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_242; obj* x_245; uint8 x_248; 
x_242 = lean::cnstr_get(x_1, 0);
lean::inc(x_242);
lean::dec(x_1);
x_245 = lean::cnstr_get(x_2, 0);
lean::inc(x_245);
lean::dec(x_2);
x_248 = l_Lean_IR_Litval_beq___main(x_242, x_245);
lean::dec(x_245);
lean::dec(x_242);
return x_248;
}
default:
{
uint8 x_253; 
lean::dec(x_1);
lean::dec(x_2);
x_253 = 0;
return x_253;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_254; obj* x_257; uint8 x_260; 
x_254 = lean::cnstr_get(x_1, 0);
lean::inc(x_254);
lean::dec(x_1);
x_257 = lean::cnstr_get(x_2, 0);
lean::inc(x_257);
lean::dec(x_2);
x_260 = l_Lean_IR_VarId_alphaEqv(x_0, x_254, x_257);
lean::dec(x_257);
return x_260;
}
default:
{
uint8 x_265; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_265 = 0;
return x_265;
}
}
}
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_266; obj* x_269; uint8 x_272; 
x_266 = lean::cnstr_get(x_1, 0);
lean::inc(x_266);
lean::dec(x_1);
x_269 = lean::cnstr_get(x_2, 0);
lean::inc(x_269);
lean::dec(x_2);
x_272 = l_Lean_IR_VarId_alphaEqv(x_0, x_266, x_269);
lean::dec(x_269);
return x_272;
}
default:
{
uint8 x_277; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_277 = 0;
return x_277;
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
obj* x_4; obj* x_5; 
x_4 = l_Lean_NameMap_contains___rarg___closed__1;
x_5 = l_RBNode_insert___rarg(x_4, x_0, x_1, x_2);
return x_5;
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
if (x_29 == 0)
{
uint8 x_35; 
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_16);
x_35 = 0;
return x_35;
}
else
{
obj* x_36; 
x_36 = l_Lean_IR_addVarRename(x_0, x_4, x_11);
x_0 = x_36;
x_1 = x_8;
x_2 = x_16;
goto _start;
}
}
}
case 12:
{
uint8 x_40; 
lean::dec(x_1);
lean::dec(x_0);
x_40 = 0;
return x_40;
}
default:
{
uint8 x_44; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_44 = 0;
return x_44;
}
}
}
case 1:
{
uint8 x_45; 
x_45 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_55; obj* x_57; uint8 x_59; obj* x_60; obj* x_62; obj* x_66; 
x_46 = lean::cnstr_get(x_1, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_1, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_1, 2);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_1, 3);
lean::inc(x_52);
lean::dec(x_1);
x_55 = lean::cnstr_get(x_2, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_2, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
x_60 = lean::cnstr_get(x_2, 2);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_2, 3);
lean::inc(x_62);
lean::dec(x_2);
lean::inc(x_0);
x_66 = l_Lean_IR_addParamsRename___main(x_0, x_48, x_57);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_74; 
lean::dec(x_0);
lean::dec(x_55);
lean::dec(x_62);
lean::dec(x_50);
lean::dec(x_52);
lean::dec(x_46);
lean::dec(x_60);
x_74 = 0;
return x_74;
}
else
{
obj* x_75; uint8 x_78; 
x_75 = lean::cnstr_get(x_66, 0);
lean::inc(x_75);
lean::dec(x_66);
x_78 = l_Lean_IR_IRType_beq___main(x_45, x_59);
if (x_78 == 0)
{
uint8 x_87; 
lean::dec(x_0);
lean::dec(x_55);
lean::dec(x_62);
lean::dec(x_75);
lean::dec(x_50);
lean::dec(x_52);
lean::dec(x_46);
lean::dec(x_60);
x_87 = 0;
return x_87;
}
else
{
uint8 x_88; 
x_88 = l_Lean_IR_Fnbody_alphaEqv___main(x_75, x_50, x_60);
if (x_88 == 0)
{
uint8 x_94; 
lean::dec(x_0);
lean::dec(x_55);
lean::dec(x_62);
lean::dec(x_52);
lean::dec(x_46);
x_94 = 0;
return x_94;
}
else
{
obj* x_95; 
x_95 = l_Lean_IR_addVarRename(x_0, x_46, x_55);
x_0 = x_95;
x_1 = x_52;
x_2 = x_62;
goto _start;
}
}
}
}
case 12:
{
uint8 x_99; 
lean::dec(x_1);
lean::dec(x_0);
x_99 = 0;
return x_99;
}
default:
{
uint8 x_103; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_103 = 0;
return x_103;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_113; obj* x_115; obj* x_117; obj* x_119; uint8 x_123; 
x_104 = lean::cnstr_get(x_1, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_1, 1);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_1, 2);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_1, 3);
lean::inc(x_110);
lean::dec(x_1);
x_113 = lean::cnstr_get(x_2, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_2, 1);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_2, 2);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_2, 3);
lean::inc(x_119);
lean::dec(x_2);
lean::inc(x_0);
x_123 = l_Lean_IR_VarId_alphaEqv(x_0, x_104, x_113);
lean::dec(x_113);
if (x_123 == 0)
{
uint8 x_132; 
lean::dec(x_110);
lean::dec(x_119);
lean::dec(x_106);
lean::dec(x_108);
lean::dec(x_115);
lean::dec(x_117);
lean::dec(x_0);
x_132 = 0;
return x_132;
}
else
{
uint8 x_133; 
x_133 = lean::nat_dec_eq(x_106, x_115);
lean::dec(x_115);
lean::dec(x_106);
if (x_133 == 0)
{
uint8 x_141; 
lean::dec(x_110);
lean::dec(x_119);
lean::dec(x_108);
lean::dec(x_117);
lean::dec(x_0);
x_141 = 0;
return x_141;
}
else
{
uint8 x_143; 
lean::inc(x_0);
x_143 = l_Lean_IR_VarId_alphaEqv(x_0, x_108, x_117);
lean::dec(x_117);
if (x_143 == 0)
{
uint8 x_148; 
lean::dec(x_110);
lean::dec(x_119);
lean::dec(x_0);
x_148 = 0;
return x_148;
}
else
{
x_1 = x_110;
x_2 = x_119;
goto _start;
}
}
}
}
case 12:
{
uint8 x_152; 
lean::dec(x_1);
lean::dec(x_0);
x_152 = 0;
return x_152;
}
default:
{
uint8 x_156; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_156 = 0;
return x_156;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_157; obj* x_159; obj* x_161; obj* x_163; obj* x_166; obj* x_168; obj* x_170; obj* x_172; uint8 x_176; 
x_157 = lean::cnstr_get(x_1, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_1, 1);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_1, 2);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_1, 3);
lean::inc(x_163);
lean::dec(x_1);
x_166 = lean::cnstr_get(x_2, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_2, 1);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_2, 2);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_2, 3);
lean::inc(x_172);
lean::dec(x_2);
lean::inc(x_0);
x_176 = l_Lean_IR_VarId_alphaEqv(x_0, x_157, x_166);
lean::dec(x_166);
if (x_176 == 0)
{
uint8 x_185; 
lean::dec(x_0);
lean::dec(x_168);
lean::dec(x_172);
lean::dec(x_163);
lean::dec(x_159);
lean::dec(x_170);
lean::dec(x_161);
x_185 = 0;
return x_185;
}
else
{
uint8 x_186; 
x_186 = lean::nat_dec_eq(x_159, x_168);
lean::dec(x_168);
lean::dec(x_159);
if (x_186 == 0)
{
uint8 x_194; 
lean::dec(x_0);
lean::dec(x_172);
lean::dec(x_163);
lean::dec(x_170);
lean::dec(x_161);
x_194 = 0;
return x_194;
}
else
{
uint8 x_196; 
lean::inc(x_0);
x_196 = l_Lean_IR_VarId_alphaEqv(x_0, x_161, x_170);
lean::dec(x_170);
if (x_196 == 0)
{
uint8 x_201; 
lean::dec(x_0);
lean::dec(x_172);
lean::dec(x_163);
x_201 = 0;
return x_201;
}
else
{
x_1 = x_163;
x_2 = x_172;
goto _start;
}
}
}
}
case 12:
{
uint8 x_205; 
lean::dec(x_1);
lean::dec(x_0);
x_205 = 0;
return x_205;
}
default:
{
uint8 x_209; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_209 = 0;
return x_209;
}
}
}
case 4:
{
uint8 x_210; 
x_210 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; obj* x_222; obj* x_224; obj* x_226; obj* x_228; uint8 x_230; obj* x_231; uint8 x_235; 
x_211 = lean::cnstr_get(x_1, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_1, 1);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_1, 2);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_1, 3);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_1, 4);
lean::inc(x_219);
lean::dec(x_1);
x_222 = lean::cnstr_get(x_2, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_2, 1);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_2, 2);
lean::inc(x_226);
x_228 = lean::cnstr_get(x_2, 3);
lean::inc(x_228);
x_230 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_231 = lean::cnstr_get(x_2, 4);
lean::inc(x_231);
lean::dec(x_2);
lean::inc(x_0);
x_235 = l_Lean_IR_VarId_alphaEqv(x_0, x_211, x_222);
lean::dec(x_222);
if (x_235 == 0)
{
uint8 x_246; 
lean::dec(x_0);
lean::dec(x_231);
lean::dec(x_226);
lean::dec(x_224);
lean::dec(x_217);
lean::dec(x_228);
lean::dec(x_215);
lean::dec(x_219);
lean::dec(x_213);
x_246 = 0;
return x_246;
}
else
{
uint8 x_247; 
x_247 = lean::nat_dec_eq(x_213, x_224);
lean::dec(x_224);
lean::dec(x_213);
if (x_247 == 0)
{
uint8 x_257; 
lean::dec(x_0);
lean::dec(x_231);
lean::dec(x_226);
lean::dec(x_217);
lean::dec(x_228);
lean::dec(x_215);
lean::dec(x_219);
x_257 = 0;
return x_257;
}
else
{
uint8 x_258; 
x_258 = lean::nat_dec_eq(x_215, x_226);
lean::dec(x_226);
lean::dec(x_215);
if (x_258 == 0)
{
uint8 x_266; 
lean::dec(x_0);
lean::dec(x_231);
lean::dec(x_217);
lean::dec(x_228);
lean::dec(x_219);
x_266 = 0;
return x_266;
}
else
{
uint8 x_268; 
lean::inc(x_0);
x_268 = l_Lean_IR_VarId_alphaEqv(x_0, x_217, x_228);
lean::dec(x_228);
if (x_268 == 0)
{
uint8 x_273; 
lean::dec(x_0);
lean::dec(x_231);
lean::dec(x_219);
x_273 = 0;
return x_273;
}
else
{
uint8 x_274; 
x_274 = l_Lean_IR_IRType_beq___main(x_210, x_230);
if (x_274 == 0)
{
uint8 x_278; 
lean::dec(x_0);
lean::dec(x_231);
lean::dec(x_219);
x_278 = 0;
return x_278;
}
else
{
x_1 = x_219;
x_2 = x_231;
goto _start;
}
}
}
}
}
}
case 12:
{
uint8 x_282; 
lean::dec(x_1);
lean::dec(x_0);
x_282 = 0;
return x_282;
}
default:
{
uint8 x_286; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_286 = 0;
return x_286;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_287; obj* x_289; obj* x_291; obj* x_294; obj* x_296; obj* x_298; uint8 x_302; 
x_287 = lean::cnstr_get(x_1, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_1, 1);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_1, 2);
lean::inc(x_291);
lean::dec(x_1);
x_294 = lean::cnstr_get(x_2, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_2, 1);
lean::inc(x_296);
x_298 = lean::cnstr_get(x_2, 2);
lean::inc(x_298);
lean::dec(x_2);
lean::inc(x_0);
x_302 = l_Lean_IR_VarId_alphaEqv(x_0, x_287, x_294);
lean::dec(x_294);
if (x_302 == 0)
{
uint8 x_309; 
lean::dec(x_298);
lean::dec(x_0);
lean::dec(x_296);
lean::dec(x_289);
lean::dec(x_291);
x_309 = 0;
return x_309;
}
else
{
uint8 x_310; 
x_310 = lean::nat_dec_eq(x_289, x_296);
lean::dec(x_296);
lean::dec(x_289);
if (x_310 == 0)
{
uint8 x_316; 
lean::dec(x_298);
lean::dec(x_0);
lean::dec(x_291);
x_316 = 0;
return x_316;
}
else
{
x_1 = x_291;
x_2 = x_298;
goto _start;
}
}
}
case 12:
{
uint8 x_320; 
lean::dec(x_1);
lean::dec(x_0);
x_320 = 0;
return x_320;
}
default:
{
uint8 x_324; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_324 = 0;
return x_324;
}
}
}
case 6:
{
uint8 x_325; 
x_325 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_326; obj* x_328; obj* x_330; obj* x_333; obj* x_335; uint8 x_337; obj* x_338; uint8 x_342; 
x_326 = lean::cnstr_get(x_1, 0);
lean::inc(x_326);
x_328 = lean::cnstr_get(x_1, 1);
lean::inc(x_328);
x_330 = lean::cnstr_get(x_1, 2);
lean::inc(x_330);
lean::dec(x_1);
x_333 = lean::cnstr_get(x_2, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_2, 1);
lean::inc(x_335);
x_337 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_338 = lean::cnstr_get(x_2, 2);
lean::inc(x_338);
lean::dec(x_2);
lean::inc(x_0);
x_342 = l_Lean_IR_VarId_alphaEqv(x_0, x_326, x_333);
lean::dec(x_333);
if (x_342 == 0)
{
uint8 x_349; 
lean::dec(x_0);
lean::dec(x_330);
lean::dec(x_338);
lean::dec(x_328);
lean::dec(x_335);
x_349 = 0;
return x_349;
}
else
{
uint8 x_350; 
x_350 = lean::nat_dec_eq(x_328, x_335);
lean::dec(x_335);
lean::dec(x_328);
if (x_350 == 0)
{
uint8 x_356; 
lean::dec(x_0);
lean::dec(x_330);
lean::dec(x_338);
x_356 = 0;
return x_356;
}
else
{
if (x_325 == 0)
{
if (x_337 == 0)
{
x_1 = x_330;
x_2 = x_338;
goto _start;
}
else
{
uint8 x_361; 
lean::dec(x_0);
lean::dec(x_330);
lean::dec(x_338);
x_361 = 0;
return x_361;
}
}
else
{
if (x_337 == 0)
{
uint8 x_365; 
lean::dec(x_0);
lean::dec(x_330);
lean::dec(x_338);
x_365 = 0;
return x_365;
}
else
{
x_1 = x_330;
x_2 = x_338;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_369; 
lean::dec(x_1);
lean::dec(x_0);
x_369 = 0;
return x_369;
}
default:
{
uint8 x_373; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_373 = 0;
return x_373;
}
}
}
case 7:
{
uint8 x_374; 
x_374 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_375; obj* x_377; obj* x_379; obj* x_382; obj* x_384; uint8 x_386; obj* x_387; uint8 x_391; 
x_375 = lean::cnstr_get(x_1, 0);
lean::inc(x_375);
x_377 = lean::cnstr_get(x_1, 1);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_1, 2);
lean::inc(x_379);
lean::dec(x_1);
x_382 = lean::cnstr_get(x_2, 0);
lean::inc(x_382);
x_384 = lean::cnstr_get(x_2, 1);
lean::inc(x_384);
x_386 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_387 = lean::cnstr_get(x_2, 2);
lean::inc(x_387);
lean::dec(x_2);
lean::inc(x_0);
x_391 = l_Lean_IR_VarId_alphaEqv(x_0, x_375, x_382);
lean::dec(x_382);
if (x_391 == 0)
{
uint8 x_398; 
lean::dec(x_379);
lean::dec(x_377);
lean::dec(x_384);
lean::dec(x_387);
lean::dec(x_0);
x_398 = 0;
return x_398;
}
else
{
uint8 x_399; 
x_399 = lean::nat_dec_eq(x_377, x_384);
lean::dec(x_384);
lean::dec(x_377);
if (x_399 == 0)
{
uint8 x_405; 
lean::dec(x_379);
lean::dec(x_387);
lean::dec(x_0);
x_405 = 0;
return x_405;
}
else
{
if (x_374 == 0)
{
if (x_386 == 0)
{
x_1 = x_379;
x_2 = x_387;
goto _start;
}
else
{
uint8 x_410; 
lean::dec(x_379);
lean::dec(x_387);
lean::dec(x_0);
x_410 = 0;
return x_410;
}
}
else
{
if (x_386 == 0)
{
uint8 x_414; 
lean::dec(x_379);
lean::dec(x_387);
lean::dec(x_0);
x_414 = 0;
return x_414;
}
else
{
x_1 = x_379;
x_2 = x_387;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_418; 
lean::dec(x_1);
lean::dec(x_0);
x_418 = 0;
return x_418;
}
default:
{
uint8 x_422; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_422 = 0;
return x_422;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_423; obj* x_425; obj* x_428; obj* x_430; uint8 x_433; 
x_423 = lean::cnstr_get(x_1, 0);
lean::inc(x_423);
x_425 = lean::cnstr_get(x_1, 1);
lean::inc(x_425);
lean::dec(x_1);
x_428 = lean::cnstr_get(x_2, 0);
lean::inc(x_428);
x_430 = lean::cnstr_get(x_2, 1);
lean::inc(x_430);
lean::dec(x_2);
x_433 = l_Lean_KVMap_eqv(x_423, x_428);
if (x_433 == 0)
{
uint8 x_437; 
lean::dec(x_430);
lean::dec(x_425);
lean::dec(x_0);
x_437 = 0;
return x_437;
}
else
{
x_1 = x_425;
x_2 = x_430;
goto _start;
}
}
case 12:
{
uint8 x_441; 
lean::dec(x_1);
lean::dec(x_0);
x_441 = 0;
return x_441;
}
default:
{
uint8 x_445; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_445 = 0;
return x_445;
}
}
}
case 9:
{
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_446; obj* x_448; obj* x_450; obj* x_453; obj* x_455; obj* x_457; uint8 x_460; 
x_446 = lean::cnstr_get(x_1, 0);
lean::inc(x_446);
x_448 = lean::cnstr_get(x_1, 1);
lean::inc(x_448);
x_450 = lean::cnstr_get(x_1, 2);
lean::inc(x_450);
lean::dec(x_1);
x_453 = lean::cnstr_get(x_2, 0);
lean::inc(x_453);
x_455 = lean::cnstr_get(x_2, 1);
lean::inc(x_455);
x_457 = lean::cnstr_get(x_2, 2);
lean::inc(x_457);
lean::dec(x_2);
x_460 = lean_name_dec_eq(x_446, x_453);
lean::dec(x_453);
lean::dec(x_446);
if (x_460 == 0)
{
uint8 x_468; 
lean::dec(x_0);
lean::dec(x_457);
lean::dec(x_455);
lean::dec(x_448);
lean::dec(x_450);
x_468 = 0;
return x_468;
}
else
{
uint8 x_470; 
lean::inc(x_0);
x_470 = l_Lean_IR_VarId_alphaEqv(x_0, x_448, x_455);
lean::dec(x_455);
if (x_470 == 0)
{
uint8 x_475; 
lean::dec(x_0);
lean::dec(x_457);
lean::dec(x_450);
x_475 = 0;
return x_475;
}
else
{
uint8 x_476; 
x_476 = l_List_isEqv___main___at_Lean_IR_Fnbody_alphaEqv___main___spec__1(x_0, x_450, x_457);
return x_476;
}
}
}
case 12:
{
uint8 x_479; 
lean::dec(x_1);
lean::dec(x_0);
x_479 = 0;
return x_479;
}
default:
{
uint8 x_483; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_483 = 0;
return x_483;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_484; obj* x_487; uint8 x_490; 
x_484 = lean::cnstr_get(x_1, 0);
lean::inc(x_484);
lean::dec(x_1);
x_487 = lean::cnstr_get(x_2, 0);
lean::inc(x_487);
lean::dec(x_2);
x_490 = l_Lean_IR_VarId_alphaEqv(x_0, x_484, x_487);
lean::dec(x_487);
return x_490;
}
case 12:
{
uint8 x_494; 
lean::dec(x_1);
lean::dec(x_0);
x_494 = 0;
return x_494;
}
default:
{
uint8 x_498; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_498 = 0;
return x_498;
}
}
}
case 11:
{
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_499; obj* x_501; obj* x_504; obj* x_506; uint8 x_509; 
x_499 = lean::cnstr_get(x_1, 0);
lean::inc(x_499);
x_501 = lean::cnstr_get(x_1, 1);
lean::inc(x_501);
lean::dec(x_1);
x_504 = lean::cnstr_get(x_2, 0);
lean::inc(x_504);
x_506 = lean::cnstr_get(x_2, 1);
lean::inc(x_506);
lean::dec(x_2);
x_509 = lean_name_dec_eq(x_499, x_504);
lean::dec(x_504);
lean::dec(x_499);
if (x_509 == 0)
{
uint8 x_515; 
lean::dec(x_506);
lean::dec(x_501);
lean::dec(x_0);
x_515 = 0;
return x_515;
}
else
{
uint8 x_516; 
x_516 = l_Lean_IR_args_alphaEqv___main(x_0, x_501, x_506);
lean::dec(x_506);
return x_516;
}
}
case 12:
{
uint8 x_520; 
lean::dec(x_1);
lean::dec(x_0);
x_520 = 0;
return x_520;
}
default:
{
uint8 x_524; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_524 = 0;
return x_524;
}
}
}
default:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 12:
{
uint8 x_526; 
x_526 = 1;
return x_526;
}
default:
{
uint8 x_528; 
lean::dec(x_2);
x_528 = 0;
return x_528;
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
uint8 x_4; 
lean::inc(x_0);
x_4 = l_Lean_NameSet_contains(x_1, x_0);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_NameMap_contains___rarg___closed__1;
x_6 = lean::box(0);
x_7 = l_RBNode_insert___rarg(x_5, x_2, x_0, x_6);
return x_7;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_Lean_NameMap_contains___rarg___closed__1;
x_5 = lean::box(0);
x_6 = l_RBNode_insert___rarg(x_4, x_2, x_0, x_5);
x_7 = lean::apply_2(x_1, x_6, x_3);
return x_7;
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
obj* x_2; obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_Lean_NameMap_contains___rarg___closed__1;
x_11 = lean::box(0);
x_12 = l_RBNode_insert___rarg(x_10, x_0, x_7, x_11);
x_0 = x_12;
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
obj* l___private_init_lean_compiler_ir_5__Seq(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::apply_2(x_1, x_2, x_5);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_6__collectArg___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; uint8 x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_3);
x_7 = l_Lean_NameSet_contains(x_1, x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = l_Lean_NameMap_contains___rarg___closed__1;
x_9 = lean::box(0);
x_10 = l_RBNode_insert___rarg(x_8, x_2, x_3, x_9);
return x_10;
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
obj* x_7; obj* x_9; uint8 x_14; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_14 = l_Lean_NameSet_contains(x_1, x_7);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = l_Lean_NameMap_contains___rarg___closed__1;
x_16 = lean::box(0);
x_17 = l_RBNode_insert___rarg(x_15, x_2, x_7, x_16);
x_18 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_9, x_1, x_17);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_7);
x_20 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_9, x_1, x_2);
return x_20;
}
}
case 3:
{
obj* x_21; uint8 x_25; 
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
lean::inc(x_21);
x_25 = l_Lean_NameSet_contains(x_1, x_21);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_Lean_NameMap_contains___rarg___closed__1;
x_27 = lean::box(0);
x_28 = l_RBNode_insert___rarg(x_26, x_2, x_21, x_27);
return x_28;
}
else
{
lean::dec(x_21);
return x_2;
}
}
case 4:
{
obj* x_30; uint8 x_34; 
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
lean::inc(x_30);
x_34 = l_Lean_NameSet_contains(x_1, x_30);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = l_Lean_NameMap_contains___rarg___closed__1;
x_36 = lean::box(0);
x_37 = l_RBNode_insert___rarg(x_35, x_2, x_30, x_36);
return x_37;
}
else
{
lean::dec(x_30);
return x_2;
}
}
case 5:
{
obj* x_39; uint8 x_43; 
x_39 = lean::cnstr_get(x_0, 1);
lean::inc(x_39);
lean::dec(x_0);
lean::inc(x_39);
x_43 = l_Lean_NameSet_contains(x_1, x_39);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_Lean_NameMap_contains___rarg___closed__1;
x_45 = lean::box(0);
x_46 = l_RBNode_insert___rarg(x_44, x_2, x_39, x_45);
return x_46;
}
else
{
lean::dec(x_39);
return x_2;
}
}
case 6:
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_0, 1);
lean::inc(x_48);
lean::dec(x_0);
x_51 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_48, x_1, x_2);
return x_51;
}
case 7:
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_0, 1);
lean::inc(x_52);
lean::dec(x_0);
x_55 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_52, x_1, x_2);
return x_55;
}
case 8:
{
obj* x_56; obj* x_58; uint8 x_63; 
x_56 = lean::cnstr_get(x_0, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_0, 1);
lean::inc(x_58);
lean::dec(x_0);
lean::inc(x_56);
lean::inc(x_1);
x_63 = l_Lean_NameSet_contains(x_1, x_56);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_64 = l_Lean_NameMap_contains___rarg___closed__1;
x_65 = lean::box(0);
x_66 = l_RBNode_insert___rarg(x_64, x_2, x_56, x_65);
x_67 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_58, x_1, x_66);
return x_67;
}
else
{
obj* x_69; 
lean::dec(x_56);
x_69 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_58, x_1, x_2);
return x_69;
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
obj* x_72; uint8 x_76; 
x_72 = lean::cnstr_get(x_0, 0);
lean::inc(x_72);
lean::dec(x_0);
lean::inc(x_72);
x_76 = l_Lean_NameSet_contains(x_1, x_72);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = l_Lean_NameMap_contains___rarg___closed__1;
x_78 = lean::box(0);
x_79 = l_RBNode_insert___rarg(x_77, x_2, x_72, x_78);
return x_79;
}
else
{
lean::dec(x_72);
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
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_9__collectFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_13; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
lean::inc(x_0);
x_13 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_9, x_0, x_1);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
obj* x_15; obj* x_18; obj* x_22; 
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
lean::inc(x_0);
x_22 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_18, x_0, x_1);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_9__collectFnBody___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_13; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
lean::inc(x_0);
x_13 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_9, x_0, x_1);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
obj* x_15; obj* x_18; obj* x_22; 
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
lean::inc(x_0);
x_22 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_18, x_0, x_1);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_9__collectFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
x_11 = l___private_init_lean_compiler_ir_8__collectExpr___main(x_5, x_1, x_2);
x_12 = l_Lean_NameMap_contains___rarg___closed__1;
x_13 = lean::box(0);
x_14 = l_RBNode_insert___rarg(x_12, x_1, x_3, x_13);
x_0 = x_7;
x_1 = x_14;
x_2 = x_11;
goto _start;
}
case 1:
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 2);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_0, 3);
lean::inc(x_22);
lean::dec(x_0);
lean::inc(x_1);
x_26 = l_List_foldl___main___at_Lean_IR_insertParams___spec__1(x_1, x_18);
x_27 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_20, x_26, x_2);
x_28 = l_Lean_NameMap_contains___rarg___closed__1;
x_29 = lean::box(0);
x_30 = l_RBNode_insert___rarg(x_28, x_1, x_16, x_29);
x_0 = x_22;
x_1 = x_30;
x_2 = x_27;
goto _start;
}
case 2:
{
obj* x_32; obj* x_34; obj* x_36; uint8 x_41; uint8 x_44; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
lean::dec(x_0);
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_Lean_NameSet_contains(x_1, x_32);
lean::inc(x_34);
lean::inc(x_1);
x_44 = l_Lean_NameSet_contains(x_1, x_34);
if (x_41 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_Lean_NameMap_contains___rarg___closed__1;
x_46 = lean::box(0);
x_47 = l_RBNode_insert___rarg(x_45, x_2, x_32, x_46);
if (x_44 == 0)
{
obj* x_48; 
x_48 = l_RBNode_insert___rarg(x_45, x_47, x_34, x_46);
x_0 = x_36;
x_2 = x_48;
goto _start;
}
else
{
lean::dec(x_34);
x_0 = x_36;
x_2 = x_47;
goto _start;
}
}
else
{
lean::dec(x_32);
if (x_44 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_Lean_NameMap_contains___rarg___closed__1;
x_54 = lean::box(0);
x_55 = l_RBNode_insert___rarg(x_53, x_2, x_34, x_54);
x_0 = x_36;
x_2 = x_55;
goto _start;
}
else
{
lean::dec(x_34);
x_0 = x_36;
goto _start;
}
}
}
case 3:
{
obj* x_59; obj* x_61; obj* x_63; uint8 x_68; uint8 x_71; 
x_59 = lean::cnstr_get(x_0, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_0, 2);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_0, 3);
lean::inc(x_63);
lean::dec(x_0);
lean::inc(x_59);
lean::inc(x_1);
x_68 = l_Lean_NameSet_contains(x_1, x_59);
lean::inc(x_61);
lean::inc(x_1);
x_71 = l_Lean_NameSet_contains(x_1, x_61);
if (x_68 == 0)
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = l_Lean_NameMap_contains___rarg___closed__1;
x_73 = lean::box(0);
x_74 = l_RBNode_insert___rarg(x_72, x_2, x_59, x_73);
if (x_71 == 0)
{
obj* x_75; 
x_75 = l_RBNode_insert___rarg(x_72, x_74, x_61, x_73);
x_0 = x_63;
x_2 = x_75;
goto _start;
}
else
{
lean::dec(x_61);
x_0 = x_63;
x_2 = x_74;
goto _start;
}
}
else
{
lean::dec(x_59);
if (x_71 == 0)
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = l_Lean_NameMap_contains___rarg___closed__1;
x_81 = lean::box(0);
x_82 = l_RBNode_insert___rarg(x_80, x_2, x_61, x_81);
x_0 = x_63;
x_2 = x_82;
goto _start;
}
else
{
lean::dec(x_61);
x_0 = x_63;
goto _start;
}
}
}
case 4:
{
obj* x_86; obj* x_88; obj* x_90; uint8 x_95; uint8 x_98; 
x_86 = lean::cnstr_get(x_0, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_0, 3);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_0, 4);
lean::inc(x_90);
lean::dec(x_0);
lean::inc(x_86);
lean::inc(x_1);
x_95 = l_Lean_NameSet_contains(x_1, x_86);
lean::inc(x_88);
lean::inc(x_1);
x_98 = l_Lean_NameSet_contains(x_1, x_88);
if (x_95 == 0)
{
obj* x_99; obj* x_100; obj* x_101; 
x_99 = l_Lean_NameMap_contains___rarg___closed__1;
x_100 = lean::box(0);
x_101 = l_RBNode_insert___rarg(x_99, x_2, x_86, x_100);
if (x_98 == 0)
{
obj* x_102; 
x_102 = l_RBNode_insert___rarg(x_99, x_101, x_88, x_100);
x_0 = x_90;
x_2 = x_102;
goto _start;
}
else
{
lean::dec(x_88);
x_0 = x_90;
x_2 = x_101;
goto _start;
}
}
else
{
lean::dec(x_86);
if (x_98 == 0)
{
obj* x_107; obj* x_108; obj* x_109; 
x_107 = l_Lean_NameMap_contains___rarg___closed__1;
x_108 = lean::box(0);
x_109 = l_RBNode_insert___rarg(x_107, x_2, x_88, x_108);
x_0 = x_90;
x_2 = x_109;
goto _start;
}
else
{
lean::dec(x_88);
x_0 = x_90;
goto _start;
}
}
}
case 8:
{
obj* x_113; 
x_113 = lean::cnstr_get(x_0, 1);
lean::inc(x_113);
lean::dec(x_0);
x_0 = x_113;
goto _start;
}
case 9:
{
obj* x_117; obj* x_119; uint8 x_124; 
x_117 = lean::cnstr_get(x_0, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_0, 2);
lean::inc(x_119);
lean::dec(x_0);
lean::inc(x_117);
lean::inc(x_1);
x_124 = l_Lean_NameSet_contains(x_1, x_117);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_125 = l_Lean_NameMap_contains___rarg___closed__1;
x_126 = lean::box(0);
x_127 = l_RBNode_insert___rarg(x_125, x_2, x_117, x_126);
x_128 = l_List_foldl___main___at___private_init_lean_compiler_ir_9__collectFnBody___main___spec__1(x_1, x_127, x_119);
return x_128;
}
else
{
obj* x_130; 
lean::dec(x_117);
x_130 = l_List_foldl___main___at___private_init_lean_compiler_ir_9__collectFnBody___main___spec__2(x_1, x_2, x_119);
return x_130;
}
}
case 10:
{
obj* x_131; uint8 x_135; 
x_131 = lean::cnstr_get(x_0, 0);
lean::inc(x_131);
lean::dec(x_0);
lean::inc(x_131);
x_135 = l_Lean_NameSet_contains(x_1, x_131);
if (x_135 == 0)
{
obj* x_136; obj* x_137; obj* x_138; 
x_136 = l_Lean_NameMap_contains___rarg___closed__1;
x_137 = lean::box(0);
x_138 = l_RBNode_insert___rarg(x_136, x_2, x_131, x_137);
return x_138;
}
else
{
lean::dec(x_131);
return x_2;
}
}
case 11:
{
obj* x_140; obj* x_142; uint8 x_147; 
x_140 = lean::cnstr_get(x_0, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_0, 1);
lean::inc(x_142);
lean::dec(x_0);
lean::inc(x_140);
lean::inc(x_1);
x_147 = l_Lean_NameSet_contains(x_1, x_140);
if (x_147 == 0)
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_148 = l_Lean_NameMap_contains___rarg___closed__1;
x_149 = lean::box(0);
x_150 = l_RBNode_insert___rarg(x_148, x_2, x_140, x_149);
x_151 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_142, x_1, x_150);
return x_151;
}
else
{
obj* x_153; 
lean::dec(x_140);
x_153 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_142, x_1, x_2);
return x_153;
}
}
case 12:
{
lean::dec(x_1);
return x_2;
}
default:
{
obj* x_155; obj* x_157; uint8 x_162; 
x_155 = lean::cnstr_get(x_0, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_0, 2);
lean::inc(x_157);
lean::dec(x_0);
lean::inc(x_155);
lean::inc(x_1);
x_162 = l_Lean_NameSet_contains(x_1, x_155);
if (x_162 == 0)
{
obj* x_163; obj* x_164; obj* x_165; 
x_163 = l_Lean_NameMap_contains___rarg___closed__1;
x_164 = lean::box(0);
x_165 = l_RBNode_insert___rarg(x_163, x_2, x_155, x_164);
x_0 = x_157;
x_2 = x_165;
goto _start;
}
else
{
lean::dec(x_155);
x_0 = x_157;
goto _start;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_9__collectFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_freeVars(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_0, x_1, x_1);
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
return w;
}
