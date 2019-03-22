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
obj* l_RBMap_insert___main___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_Litval_beq___main___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
uint8 l_Lean_IR_Alt_alphaEqv(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq(uint8, uint8);
uint8 l_Lean_IR_Arg_alphaEqv(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_RBMap_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_addParamRename(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_HasBeq;
obj* l___private_init_lean_compiler_ir_8__collectExpr___main(obj*, obj*, obj*);
uint8 l_Lean_IR_Alt_isPure___main(obj*);
obj* l___private_init_lean_compiler_ir_3__withBv(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_5__Seq(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_insertParams(obj*, obj*);
uint8 l_Lean_IR_Fnbody_beq(obj*, obj*);
uint8 l_Lean_IR_Alts_isPure___main(obj*);
obj* l___private_init_lean_compiler_ir_8__collectExpr(obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_beq(obj*, obj*);
obj* l_Lean_IR_Fnbody_HasBeq;
obj* l___private_init_lean_compiler_ir_9__collectFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_Alt_default(obj*);
obj* l_Lean_IR_Fnbody_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Fnbody_isPure___main___boxed(obj*);
obj* l_Lean_IR_Alts_isPure___boxed(obj*);
uint8 l_Lean_IR_Fnbody_isPure___main(obj*);
obj* l_Lean_IR_VarId_hasAeqv;
uint8 l_Lean_NameSet_contains(obj*, obj*);
uint8 l_Lean_IR_Expr_isPure___main(obj*);
obj* l___private_init_lean_compiler_ir_1__skip___boxed(obj*);
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_2__collectVar(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip(obj*);
obj* l___private_init_lean_compiler_ir_6__collectArg___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_6__collectArg(obj*, obj*, obj*);
obj* l_Lean_IR_freeVars(obj*);
uint8 l_Lean_IR_Litval_beq(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_Alt_isPure(obj*);
obj* l_Lean_IR_Alt_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Alt_isPure___boxed(obj*);
obj* l_Lean_IR_args_hasAeqv;
obj* l_Lean_IR_Alts_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_args_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Expr_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_Alt_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Fnbody_alphaEqv(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Lean_IR_Alts_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_Litval_HasBeq;
uint8 l_Lean_IR_Litval_beq___main(obj*, obj*);
uint8 l_Lean_KVMap_eqv(obj*, obj*);
obj* l_Lean_IR_Expr_hasAeqv;
obj* l_Lean_IR_args_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_HasBeq;
uint8 l_Lean_IR_Alts_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___boxed(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_Alts_isPure___main___boxed(obj*);
obj* l_Lean_IR_Litval_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Alt_isPure___main___boxed(obj*);
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArgs___main(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___main___boxed(obj*);
obj* l_RBMap_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
obj* l_Lean_IR_addVarRename(obj*, obj*, obj*);
obj* l_Lean_IR_Fnbody_isPure___boxed(obj*);
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
obj* l_Lean_IR_Alt_ctor(obj*, obj*);
obj* l___private_init_lean_compiler_ir_9__collectAlt___main(obj*, obj*, obj*);
obj* l_Lean_IR_MData_HasEmptyc;
obj* l___private_init_lean_compiler_ir_9__collectFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg___boxed(obj*);
obj* l_Lean_IR_Fnbody_beq___boxed(obj*, obj*);
uint8 l_Lean_IR_Fnbody_isPure(obj*);
uint8 l_Lean_IR_Alts_isPure(obj*);
obj* l___private_init_lean_compiler_ir_4__withParams(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_9__collectAlt(obj*, obj*, obj*);
uint8 l_Lean_IR_Alt_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_MData_empty;
obj* l___private_init_lean_compiler_ir_9__collectAlts___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_9__collectAlts(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_beq___main___boxed(obj*, obj*);
obj* l_Lean_IR_Alts_alphaEqv___boxed(obj*, obj*, obj*);
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::string_dec_eq(x_9, x_10);
if (x_11 == 0)
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
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
return x_3;
}
else
{
x_0 = x_2;
goto _start;
}
}
case 1:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_Lean_IR_Fnbody_isPure___main(x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
x_0 = x_6;
goto _start;
}
}
case 3:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_0, 3);
x_0 = x_9;
goto _start;
}
case 4:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 4);
x_0 = x_11;
goto _start;
}
case 8:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 1);
x_0 = x_13;
goto _start;
}
case 9:
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_0, 2);
x_16 = l_Lean_IR_Alts_isPure___main(x_15);
return x_16;
}
case 10:
{
uint8 x_17; 
x_17 = 1;
return x_17;
}
case 11:
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
case 12:
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
default:
{
uint8 x_20; 
x_20 = 0;
return x_20;
}
}
}
}
uint8 l_Lean_IR_Alts_isPure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = l_Lean_IR_Alt_isPure___main(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
x_0 = x_3;
goto _start;
}
}
}
}
uint8 l_Lean_IR_Alt_isPure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; uint8 x_2; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = l_Lean_IR_Fnbody_isPure___main(x_1);
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
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
obj* l_Lean_IR_Alts_isPure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Alts_isPure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_Alt_isPure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Alt_isPure___main(x_0);
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
uint8 l_Lean_IR_Alts_isPure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Alts_isPure___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Alts_isPure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Alts_isPure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_Alt_isPure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Alt_isPure___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Alt_isPure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Alt_isPure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
uint8 l_Lean_IR_VarId_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = lean_name_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
else
{
obj* x_7; uint8 x_10; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_10 = lean_name_dec_eq(x_7, x_2);
lean::dec(x_7);
if (x_10 == 0)
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
obj* l_RBMap_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_0, x_1);
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
lean::dec(x_0);
return x_13;
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
lean::dec(x_0);
return x_7;
}
else
{
uint8 x_9; 
x_9 = l_Lean_IR_args_alphaEqv___main(x_0, x_4, x_6);
return x_9;
}
}
default:
{
uint8 x_11; 
lean::dec(x_0);
x_11 = 0;
return x_11;
}
}
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = l_Lean_IR_VarId_alphaEqv(x_0, x_12, x_13);
return x_14;
}
default:
{
uint8 x_16; 
lean::dec(x_0);
x_16 = 0;
return x_16;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_24; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::cnstr_get(x_1, 1);
x_19 = lean::cnstr_get(x_1, 2);
x_20 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get(x_2, 1);
x_22 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_24 = l_Lean_IR_VarId_alphaEqv(x_0, x_17, x_20);
if (x_24 == 0)
{
if (x_24 == 0)
{
lean::dec(x_0);
return x_24;
}
else
{
uint8 x_26; 
x_26 = l_Lean_IR_args_alphaEqv___main(x_0, x_19, x_22);
return x_26;
}
}
else
{
uint8 x_27; 
x_27 = l_Lean_IR_CtorInfo_beq___main(x_18, x_21);
if (x_27 == 0)
{
lean::dec(x_0);
return x_27;
}
else
{
uint8 x_29; 
x_29 = l_Lean_IR_args_alphaEqv___main(x_0, x_19, x_22);
return x_29;
}
}
}
default:
{
uint8 x_31; 
lean::dec(x_0);
x_31 = 0;
return x_31;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_32 = lean::cnstr_get(x_1, 0);
x_33 = lean::cnstr_get(x_1, 1);
x_34 = lean::cnstr_get(x_2, 0);
x_35 = lean::cnstr_get(x_2, 1);
x_36 = lean::nat_dec_eq(x_32, x_34);
if (x_36 == 0)
{
uint8 x_38; 
lean::dec(x_0);
x_38 = 0;
return x_38;
}
else
{
uint8 x_39; 
x_39 = l_Lean_IR_VarId_alphaEqv(x_0, x_33, x_35);
return x_39;
}
}
default:
{
uint8 x_41; 
lean::dec(x_0);
x_41 = 0;
return x_41;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; 
x_42 = lean::cnstr_get(x_1, 0);
x_43 = lean::cnstr_get(x_1, 1);
x_44 = lean::cnstr_get(x_2, 0);
x_45 = lean::cnstr_get(x_2, 1);
x_46 = lean::nat_dec_eq(x_42, x_44);
if (x_46 == 0)
{
uint8 x_48; 
lean::dec(x_0);
x_48 = 0;
return x_48;
}
else
{
uint8 x_49; 
x_49 = l_Lean_IR_VarId_alphaEqv(x_0, x_43, x_45);
return x_49;
}
}
default:
{
uint8 x_51; 
lean::dec(x_0);
x_51 = 0;
return x_51;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_1, 0);
x_53 = lean::cnstr_get(x_1, 1);
x_54 = lean::cnstr_get(x_2, 0);
x_55 = lean::cnstr_get(x_2, 1);
x_56 = lean::nat_dec_eq(x_52, x_54);
if (x_56 == 0)
{
uint8 x_58; 
lean::dec(x_0);
x_58 = 0;
return x_58;
}
else
{
uint8 x_59; 
x_59 = l_Lean_IR_VarId_alphaEqv(x_0, x_53, x_55);
return x_59;
}
}
default:
{
uint8 x_61; 
lean::dec(x_0);
x_61 = 0;
return x_61;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; uint8 x_66; 
x_62 = lean::cnstr_get(x_1, 0);
x_63 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_2, 0);
x_65 = lean::cnstr_get(x_2, 1);
x_66 = lean_name_dec_eq(x_62, x_64);
if (x_66 == 0)
{
uint8 x_68; 
lean::dec(x_0);
x_68 = 0;
return x_68;
}
else
{
uint8 x_69; 
x_69 = l_Lean_IR_args_alphaEqv___main(x_0, x_63, x_65);
return x_69;
}
}
default:
{
uint8 x_71; 
lean::dec(x_0);
x_71 = 0;
return x_71;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_72; obj* x_73; obj* x_74; uint8 x_75; 
x_72 = lean::cnstr_get(x_1, 0);
x_73 = lean::cnstr_get(x_2, 0);
x_74 = lean::cnstr_get(x_2, 1);
x_75 = lean_name_dec_eq(x_72, x_73);
if (x_75 == 0)
{
uint8 x_77; 
lean::dec(x_0);
x_77 = 0;
return x_77;
}
else
{
uint8 x_78; 
x_78 = l_Lean_IR_args_alphaEqv___main(x_0, x_74, x_74);
return x_78;
}
}
default:
{
uint8 x_80; 
lean::dec(x_0);
x_80 = 0;
return x_80;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; uint8 x_86; 
x_81 = lean::cnstr_get(x_1, 0);
x_82 = lean::cnstr_get(x_1, 1);
x_83 = lean::cnstr_get(x_2, 0);
x_84 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_86 = l_Lean_IR_VarId_alphaEqv(x_0, x_81, x_83);
if (x_86 == 0)
{
lean::dec(x_0);
return x_86;
}
else
{
uint8 x_88; 
x_88 = l_Lean_IR_args_alphaEqv___main(x_0, x_82, x_84);
return x_88;
}
}
default:
{
uint8 x_90; 
lean::dec(x_0);
x_90 = 0;
return x_90;
}
}
}
case 9:
{
uint8 x_91; 
x_91 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_92; uint8 x_93; obj* x_94; uint8 x_95; 
x_92 = lean::cnstr_get(x_1, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_94 = lean::cnstr_get(x_2, 0);
x_95 = l_Lean_IR_IRType_beq___main(x_91, x_93);
if (x_95 == 0)
{
lean::dec(x_0);
return x_95;
}
else
{
uint8 x_97; 
x_97 = l_Lean_IR_VarId_alphaEqv(x_0, x_92, x_94);
return x_97;
}
}
default:
{
uint8 x_99; 
lean::dec(x_0);
x_99 = 0;
return x_99;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_100; obj* x_101; uint8 x_102; 
x_100 = lean::cnstr_get(x_1, 0);
x_101 = lean::cnstr_get(x_2, 0);
x_102 = l_Lean_IR_VarId_alphaEqv(x_0, x_100, x_101);
return x_102;
}
default:
{
uint8 x_104; 
lean::dec(x_0);
x_104 = 0;
return x_104;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_106; obj* x_107; uint8 x_108; 
x_106 = lean::cnstr_get(x_1, 0);
x_107 = lean::cnstr_get(x_2, 0);
x_108 = l_Lean_IR_Litval_beq___main(x_106, x_107);
return x_108;
}
default:
{
uint8 x_109; 
x_109 = 0;
return x_109;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_110; obj* x_111; uint8 x_112; 
x_110 = lean::cnstr_get(x_1, 0);
x_111 = lean::cnstr_get(x_2, 0);
x_112 = l_Lean_IR_VarId_alphaEqv(x_0, x_110, x_111);
return x_112;
}
default:
{
uint8 x_114; 
lean::dec(x_0);
x_114 = 0;
return x_114;
}
}
}
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_115; obj* x_116; uint8 x_117; 
x_115 = lean::cnstr_get(x_1, 0);
x_116 = lean::cnstr_get(x_2, 0);
x_117 = l_Lean_IR_VarId_alphaEqv(x_0, x_115, x_116);
return x_117;
}
default:
{
uint8 x_119; 
lean::dec(x_0);
x_119 = 0;
return x_119;
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
x_4 = l_RBMap_insert___main___at_Lean_NameMap_insert___spec__1___rarg(x_0, x_1, x_2);
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
obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = l_Lean_IR_addVarRename(x_0, x_10, x_13);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8 x_18; uint8 x_19; 
x_18 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_19 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_18 == 0)
{
if (x_19 == 0)
{
if (x_5 == 0)
{
obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_30; obj* x_31; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_2, 0);
lean::inc(x_27);
lean::dec(x_2);
x_30 = l_Lean_IR_addVarRename(x_0, x_24, x_27);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
else
{
obj* x_35; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_35 = lean::box(0);
return x_35;
}
}
else
{
if (x_19 == 0)
{
obj* x_39; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_39 = lean::box(0);
return x_39;
}
else
{
if (x_5 == 0)
{
obj* x_43; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_43 = lean::box(0);
return x_43;
}
else
{
obj* x_44; obj* x_47; obj* x_50; obj* x_51; 
x_44 = lean::cnstr_get(x_1, 0);
lean::inc(x_44);
lean::dec(x_1);
x_47 = lean::cnstr_get(x_2, 0);
lean::inc(x_47);
lean::dec(x_2);
x_50 = l_Lean_IR_addVarRename(x_0, x_44, x_47);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
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
lean::dec(x_6);
lean::dec(x_14);
if (x_19 == 0)
{
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_16);
return x_19;
}
else
{
obj* x_27; 
x_27 = l_Lean_IR_addVarRename(x_0, x_4, x_11);
x_0 = x_27;
x_1 = x_8;
x_2 = x_16;
goto _start;
}
}
else
{
uint8 x_30; 
lean::inc(x_0);
x_30 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_6, x_14);
lean::dec(x_14);
lean::dec(x_6);
if (x_30 == 0)
{
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_16);
return x_30;
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
lean::dec(x_77);
lean::dec(x_52);
lean::dec(x_62);
if (x_80 == 0)
{
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_48);
lean::dec(x_57);
return x_80;
}
else
{
obj* x_89; 
x_89 = l_Lean_IR_addVarRename(x_0, x_48, x_57);
x_0 = x_89;
x_1 = x_54;
x_2 = x_64;
goto _start;
}
}
else
{
uint8 x_91; 
x_91 = l_Lean_IR_Fnbody_alphaEqv___main(x_77, x_52, x_62);
if (x_91 == 0)
{
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_48);
lean::dec(x_57);
return x_91;
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
lean::dec(x_108);
lean::dec(x_117);
if (x_125 == 0)
{
lean::dec(x_119);
lean::dec(x_110);
if (x_125 == 0)
{
lean::dec(x_121);
lean::dec(x_112);
lean::dec(x_0);
return x_125;
}
else
{
x_1 = x_112;
x_2 = x_121;
goto _start;
}
}
else
{
uint8 x_137; 
lean::inc(x_0);
x_137 = l_Lean_IR_VarId_alphaEqv(x_0, x_110, x_119);
lean::dec(x_119);
lean::dec(x_110);
if (x_137 == 0)
{
lean::dec(x_121);
lean::dec(x_112);
lean::dec(x_0);
return x_137;
}
else
{
x_1 = x_112;
x_2 = x_121;
goto _start;
}
}
}
else
{
uint8 x_144; 
x_144 = lean::nat_dec_eq(x_108, x_117);
lean::dec(x_117);
lean::dec(x_108);
if (x_144 == 0)
{
uint8 x_152; 
lean::dec(x_119);
lean::dec(x_121);
lean::dec(x_110);
lean::dec(x_112);
lean::dec(x_0);
x_152 = 0;
return x_152;
}
else
{
uint8 x_154; 
lean::inc(x_0);
x_154 = l_Lean_IR_VarId_alphaEqv(x_0, x_110, x_119);
lean::dec(x_119);
lean::dec(x_110);
if (x_154 == 0)
{
lean::dec(x_121);
lean::dec(x_112);
lean::dec(x_0);
return x_154;
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
uint8 x_163; 
lean::dec(x_1);
lean::dec(x_0);
x_163 = 0;
return x_163;
}
default:
{
uint8 x_167; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_167 = 0;
return x_167;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_168; obj* x_170; obj* x_172; obj* x_174; obj* x_177; obj* x_179; obj* x_181; obj* x_183; uint8 x_187; 
x_168 = lean::cnstr_get(x_1, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_1, 1);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_1, 2);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_1, 3);
lean::inc(x_174);
lean::dec(x_1);
x_177 = lean::cnstr_get(x_2, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_2, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_2, 2);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_2, 3);
lean::inc(x_183);
lean::dec(x_2);
lean::inc(x_0);
x_187 = l_Lean_IR_VarId_alphaEqv(x_0, x_168, x_177);
lean::dec(x_177);
lean::dec(x_168);
if (x_187 == 0)
{
lean::dec(x_179);
lean::dec(x_170);
if (x_187 == 0)
{
lean::dec(x_181);
lean::dec(x_172);
if (x_187 == 0)
{
lean::dec(x_174);
lean::dec(x_0);
lean::dec(x_183);
return x_187;
}
else
{
x_1 = x_174;
x_2 = x_183;
goto _start;
}
}
else
{
uint8 x_199; 
lean::inc(x_0);
x_199 = l_Lean_IR_VarId_alphaEqv(x_0, x_172, x_181);
lean::dec(x_181);
lean::dec(x_172);
if (x_199 == 0)
{
lean::dec(x_174);
lean::dec(x_0);
lean::dec(x_183);
return x_199;
}
else
{
x_1 = x_174;
x_2 = x_183;
goto _start;
}
}
}
else
{
uint8 x_206; 
x_206 = lean::nat_dec_eq(x_170, x_179);
lean::dec(x_179);
lean::dec(x_170);
if (x_206 == 0)
{
uint8 x_214; 
lean::dec(x_174);
lean::dec(x_0);
lean::dec(x_183);
lean::dec(x_181);
lean::dec(x_172);
x_214 = 0;
return x_214;
}
else
{
uint8 x_216; 
lean::inc(x_0);
x_216 = l_Lean_IR_VarId_alphaEqv(x_0, x_172, x_181);
lean::dec(x_181);
lean::dec(x_172);
if (x_216 == 0)
{
lean::dec(x_174);
lean::dec(x_0);
lean::dec(x_183);
return x_216;
}
else
{
x_1 = x_174;
x_2 = x_183;
goto _start;
}
}
}
}
case 12:
{
uint8 x_225; 
lean::dec(x_1);
lean::dec(x_0);
x_225 = 0;
return x_225;
}
default:
{
uint8 x_229; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_229 = 0;
return x_229;
}
}
}
case 4:
{
uint8 x_230; 
x_230 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_231; obj* x_233; obj* x_235; obj* x_237; obj* x_239; obj* x_242; obj* x_244; obj* x_246; obj* x_248; uint8 x_250; obj* x_251; uint8 x_254; uint8 x_256; uint8 x_259; 
x_231 = lean::cnstr_get(x_1, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_1, 1);
lean::inc(x_233);
x_235 = lean::cnstr_get(x_1, 2);
lean::inc(x_235);
x_237 = lean::cnstr_get(x_1, 3);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_1, 4);
lean::inc(x_239);
lean::dec(x_1);
x_242 = lean::cnstr_get(x_2, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_2, 1);
lean::inc(x_244);
x_246 = lean::cnstr_get(x_2, 2);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_2, 3);
lean::inc(x_248);
x_250 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_251 = lean::cnstr_get(x_2, 4);
lean::inc(x_251);
lean::dec(x_2);
lean::inc(x_0);
x_259 = l_Lean_IR_VarId_alphaEqv(x_0, x_231, x_242);
lean::dec(x_242);
lean::dec(x_231);
if (x_259 == 0)
{
lean::dec(x_244);
lean::dec(x_233);
if (x_259 == 0)
{
lean::dec(x_246);
lean::dec(x_235);
x_254 = x_259;
goto lbl_255;
}
else
{
x_256 = x_259;
goto lbl_257;
}
}
else
{
uint8 x_266; 
x_266 = lean::nat_dec_eq(x_233, x_244);
lean::dec(x_244);
lean::dec(x_233);
if (x_266 == 0)
{
uint8 x_271; 
lean::dec(x_246);
lean::dec(x_235);
x_271 = 0;
x_254 = x_271;
goto lbl_255;
}
else
{
if (x_259 == 0)
{
lean::dec(x_246);
lean::dec(x_235);
x_254 = x_259;
goto lbl_255;
}
else
{
x_256 = x_259;
goto lbl_257;
}
}
}
lbl_255:
{
if (x_254 == 0)
{
lean::dec(x_237);
lean::dec(x_248);
if (x_254 == 0)
{
if (x_254 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_254;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
else
{
uint8 x_280; 
x_280 = l_Lean_IR_IRType_beq___main(x_230, x_250);
if (x_280 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_280;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
}
else
{
uint8 x_286; 
lean::inc(x_0);
x_286 = l_Lean_IR_VarId_alphaEqv(x_0, x_237, x_248);
lean::dec(x_248);
lean::dec(x_237);
if (x_286 == 0)
{
if (x_286 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_286;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
else
{
uint8 x_293; 
x_293 = l_Lean_IR_IRType_beq___main(x_230, x_250);
if (x_293 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_293;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
}
}
lbl_257:
{
uint8 x_298; 
x_298 = lean::nat_dec_eq(x_235, x_246);
lean::dec(x_246);
lean::dec(x_235);
if (x_298 == 0)
{
uint8 x_306; 
lean::dec(x_239);
lean::dec(x_237);
lean::dec(x_248);
lean::dec(x_251);
lean::dec(x_0);
x_306 = 0;
return x_306;
}
else
{
if (x_256 == 0)
{
lean::dec(x_237);
lean::dec(x_248);
if (x_256 == 0)
{
if (x_256 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_256;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
else
{
uint8 x_313; 
x_313 = l_Lean_IR_IRType_beq___main(x_230, x_250);
if (x_313 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_313;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
}
else
{
uint8 x_319; 
lean::inc(x_0);
x_319 = l_Lean_IR_VarId_alphaEqv(x_0, x_237, x_248);
lean::dec(x_248);
lean::dec(x_237);
if (x_319 == 0)
{
if (x_319 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_319;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
else
{
uint8 x_326; 
x_326 = l_Lean_IR_IRType_beq___main(x_230, x_250);
if (x_326 == 0)
{
lean::dec(x_239);
lean::dec(x_251);
lean::dec(x_0);
return x_326;
}
else
{
x_1 = x_239;
x_2 = x_251;
goto _start;
}
}
}
}
}
}
case 12:
{
uint8 x_333; 
lean::dec(x_1);
lean::dec(x_0);
x_333 = 0;
return x_333;
}
default:
{
uint8 x_337; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_337 = 0;
return x_337;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_338; obj* x_340; obj* x_342; obj* x_345; obj* x_347; obj* x_349; uint8 x_353; 
x_338 = lean::cnstr_get(x_1, 0);
lean::inc(x_338);
x_340 = lean::cnstr_get(x_1, 1);
lean::inc(x_340);
x_342 = lean::cnstr_get(x_1, 2);
lean::inc(x_342);
lean::dec(x_1);
x_345 = lean::cnstr_get(x_2, 0);
lean::inc(x_345);
x_347 = lean::cnstr_get(x_2, 1);
lean::inc(x_347);
x_349 = lean::cnstr_get(x_2, 2);
lean::inc(x_349);
lean::dec(x_2);
lean::inc(x_0);
x_353 = l_Lean_IR_VarId_alphaEqv(x_0, x_338, x_345);
lean::dec(x_345);
lean::dec(x_338);
if (x_353 == 0)
{
lean::dec(x_340);
lean::dec(x_347);
if (x_353 == 0)
{
lean::dec(x_0);
lean::dec(x_342);
lean::dec(x_349);
return x_353;
}
else
{
x_1 = x_342;
x_2 = x_349;
goto _start;
}
}
else
{
uint8 x_362; 
x_362 = lean::nat_dec_eq(x_340, x_347);
lean::dec(x_347);
lean::dec(x_340);
if (x_362 == 0)
{
uint8 x_368; 
lean::dec(x_0);
lean::dec(x_342);
lean::dec(x_349);
x_368 = 0;
return x_368;
}
else
{
x_1 = x_342;
x_2 = x_349;
goto _start;
}
}
}
case 12:
{
uint8 x_372; 
lean::dec(x_1);
lean::dec(x_0);
x_372 = 0;
return x_372;
}
default:
{
uint8 x_376; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_376 = 0;
return x_376;
}
}
}
case 6:
{
uint8 x_377; 
x_377 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_378; obj* x_380; obj* x_382; obj* x_385; obj* x_387; uint8 x_389; obj* x_390; uint8 x_394; 
x_378 = lean::cnstr_get(x_1, 0);
lean::inc(x_378);
x_380 = lean::cnstr_get(x_1, 1);
lean::inc(x_380);
x_382 = lean::cnstr_get(x_1, 2);
lean::inc(x_382);
lean::dec(x_1);
x_385 = lean::cnstr_get(x_2, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_2, 1);
lean::inc(x_387);
x_389 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_390 = lean::cnstr_get(x_2, 2);
lean::inc(x_390);
lean::dec(x_2);
lean::inc(x_0);
x_394 = l_Lean_IR_VarId_alphaEqv(x_0, x_378, x_385);
lean::dec(x_385);
lean::dec(x_378);
if (x_394 == 0)
{
lean::dec(x_380);
lean::dec(x_387);
if (x_394 == 0)
{
if (x_394 == 0)
{
lean::dec(x_0);
lean::dec(x_382);
lean::dec(x_390);
return x_394;
}
else
{
x_1 = x_382;
x_2 = x_390;
goto _start;
}
}
else
{
if (x_377 == 0)
{
if (x_389 == 0)
{
x_1 = x_382;
x_2 = x_390;
goto _start;
}
else
{
uint8 x_407; 
lean::dec(x_0);
lean::dec(x_382);
lean::dec(x_390);
x_407 = 0;
return x_407;
}
}
else
{
if (x_389 == 0)
{
uint8 x_411; 
lean::dec(x_0);
lean::dec(x_382);
lean::dec(x_390);
x_411 = 0;
return x_411;
}
else
{
x_1 = x_382;
x_2 = x_390;
goto _start;
}
}
}
}
else
{
uint8 x_413; 
x_413 = lean::nat_dec_eq(x_380, x_387);
lean::dec(x_387);
lean::dec(x_380);
if (x_413 == 0)
{
uint8 x_419; 
lean::dec(x_0);
lean::dec(x_382);
lean::dec(x_390);
x_419 = 0;
return x_419;
}
else
{
if (x_377 == 0)
{
if (x_389 == 0)
{
x_1 = x_382;
x_2 = x_390;
goto _start;
}
else
{
uint8 x_424; 
lean::dec(x_0);
lean::dec(x_382);
lean::dec(x_390);
x_424 = 0;
return x_424;
}
}
else
{
if (x_389 == 0)
{
uint8 x_428; 
lean::dec(x_0);
lean::dec(x_382);
lean::dec(x_390);
x_428 = 0;
return x_428;
}
else
{
x_1 = x_382;
x_2 = x_390;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_432; 
lean::dec(x_1);
lean::dec(x_0);
x_432 = 0;
return x_432;
}
default:
{
uint8 x_436; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_436 = 0;
return x_436;
}
}
}
case 7:
{
uint8 x_437; 
x_437 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_438; obj* x_440; obj* x_442; obj* x_445; obj* x_447; uint8 x_449; obj* x_450; uint8 x_454; 
x_438 = lean::cnstr_get(x_1, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get(x_1, 1);
lean::inc(x_440);
x_442 = lean::cnstr_get(x_1, 2);
lean::inc(x_442);
lean::dec(x_1);
x_445 = lean::cnstr_get(x_2, 0);
lean::inc(x_445);
x_447 = lean::cnstr_get(x_2, 1);
lean::inc(x_447);
x_449 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_450 = lean::cnstr_get(x_2, 2);
lean::inc(x_450);
lean::dec(x_2);
lean::inc(x_0);
x_454 = l_Lean_IR_VarId_alphaEqv(x_0, x_438, x_445);
lean::dec(x_445);
lean::dec(x_438);
if (x_454 == 0)
{
lean::dec(x_447);
lean::dec(x_440);
if (x_454 == 0)
{
if (x_454 == 0)
{
lean::dec(x_0);
lean::dec(x_442);
lean::dec(x_450);
return x_454;
}
else
{
x_1 = x_442;
x_2 = x_450;
goto _start;
}
}
else
{
if (x_437 == 0)
{
if (x_449 == 0)
{
x_1 = x_442;
x_2 = x_450;
goto _start;
}
else
{
uint8 x_467; 
lean::dec(x_0);
lean::dec(x_442);
lean::dec(x_450);
x_467 = 0;
return x_467;
}
}
else
{
if (x_449 == 0)
{
uint8 x_471; 
lean::dec(x_0);
lean::dec(x_442);
lean::dec(x_450);
x_471 = 0;
return x_471;
}
else
{
x_1 = x_442;
x_2 = x_450;
goto _start;
}
}
}
}
else
{
uint8 x_473; 
x_473 = lean::nat_dec_eq(x_440, x_447);
lean::dec(x_447);
lean::dec(x_440);
if (x_473 == 0)
{
uint8 x_479; 
lean::dec(x_0);
lean::dec(x_442);
lean::dec(x_450);
x_479 = 0;
return x_479;
}
else
{
if (x_437 == 0)
{
if (x_449 == 0)
{
x_1 = x_442;
x_2 = x_450;
goto _start;
}
else
{
uint8 x_484; 
lean::dec(x_0);
lean::dec(x_442);
lean::dec(x_450);
x_484 = 0;
return x_484;
}
}
else
{
if (x_449 == 0)
{
uint8 x_488; 
lean::dec(x_0);
lean::dec(x_442);
lean::dec(x_450);
x_488 = 0;
return x_488;
}
else
{
x_1 = x_442;
x_2 = x_450;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_492; 
lean::dec(x_1);
lean::dec(x_0);
x_492 = 0;
return x_492;
}
default:
{
uint8 x_496; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_496 = 0;
return x_496;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_497; obj* x_499; obj* x_502; obj* x_504; uint8 x_507; 
x_497 = lean::cnstr_get(x_1, 0);
lean::inc(x_497);
x_499 = lean::cnstr_get(x_1, 1);
lean::inc(x_499);
lean::dec(x_1);
x_502 = lean::cnstr_get(x_2, 0);
lean::inc(x_502);
x_504 = lean::cnstr_get(x_2, 1);
lean::inc(x_504);
lean::dec(x_2);
x_507 = l_Lean_KVMap_eqv(x_497, x_502);
if (x_507 == 0)
{
lean::dec(x_0);
lean::dec(x_499);
lean::dec(x_504);
return x_507;
}
else
{
x_1 = x_499;
x_2 = x_504;
goto _start;
}
}
case 12:
{
uint8 x_514; 
lean::dec(x_1);
lean::dec(x_0);
x_514 = 0;
return x_514;
}
default:
{
uint8 x_518; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_518 = 0;
return x_518;
}
}
}
case 9:
{
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_519; obj* x_521; obj* x_523; obj* x_526; obj* x_528; obj* x_530; uint8 x_533; 
x_519 = lean::cnstr_get(x_1, 0);
lean::inc(x_519);
x_521 = lean::cnstr_get(x_1, 1);
lean::inc(x_521);
x_523 = lean::cnstr_get(x_1, 2);
lean::inc(x_523);
lean::dec(x_1);
x_526 = lean::cnstr_get(x_2, 0);
lean::inc(x_526);
x_528 = lean::cnstr_get(x_2, 1);
lean::inc(x_528);
x_530 = lean::cnstr_get(x_2, 2);
lean::inc(x_530);
lean::dec(x_2);
x_533 = lean_name_dec_eq(x_519, x_526);
lean::dec(x_526);
lean::dec(x_519);
if (x_533 == 0)
{
uint8 x_541; 
lean::dec(x_0);
lean::dec(x_530);
lean::dec(x_528);
lean::dec(x_521);
lean::dec(x_523);
x_541 = 0;
return x_541;
}
else
{
uint8 x_543; 
lean::inc(x_0);
x_543 = l_Lean_IR_VarId_alphaEqv(x_0, x_521, x_528);
lean::dec(x_528);
lean::dec(x_521);
if (x_543 == 0)
{
lean::dec(x_0);
lean::dec(x_530);
lean::dec(x_523);
return x_543;
}
else
{
uint8 x_549; 
x_549 = l_Lean_IR_Alts_alphaEqv___main(x_0, x_523, x_530);
return x_549;
}
}
}
case 12:
{
uint8 x_552; 
lean::dec(x_1);
lean::dec(x_0);
x_552 = 0;
return x_552;
}
default:
{
uint8 x_556; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_556 = 0;
return x_556;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_557; obj* x_560; uint8 x_563; 
x_557 = lean::cnstr_get(x_1, 0);
lean::inc(x_557);
lean::dec(x_1);
x_560 = lean::cnstr_get(x_2, 0);
lean::inc(x_560);
lean::dec(x_2);
x_563 = l_Lean_IR_VarId_alphaEqv(x_0, x_557, x_560);
lean::dec(x_560);
lean::dec(x_557);
return x_563;
}
case 12:
{
uint8 x_568; 
lean::dec(x_1);
lean::dec(x_0);
x_568 = 0;
return x_568;
}
default:
{
uint8 x_572; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_572 = 0;
return x_572;
}
}
}
case 11:
{
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_573; obj* x_575; obj* x_578; obj* x_580; uint8 x_583; 
x_573 = lean::cnstr_get(x_1, 0);
lean::inc(x_573);
x_575 = lean::cnstr_get(x_1, 1);
lean::inc(x_575);
lean::dec(x_1);
x_578 = lean::cnstr_get(x_2, 0);
lean::inc(x_578);
x_580 = lean::cnstr_get(x_2, 1);
lean::inc(x_580);
lean::dec(x_2);
x_583 = lean_name_dec_eq(x_573, x_578);
lean::dec(x_578);
lean::dec(x_573);
if (x_583 == 0)
{
uint8 x_589; 
lean::dec(x_0);
lean::dec(x_580);
lean::dec(x_575);
x_589 = 0;
return x_589;
}
else
{
uint8 x_590; 
x_590 = l_Lean_IR_args_alphaEqv___main(x_0, x_575, x_580);
lean::dec(x_580);
lean::dec(x_575);
return x_590;
}
}
case 12:
{
uint8 x_595; 
lean::dec(x_1);
lean::dec(x_0);
x_595 = 0;
return x_595;
}
default:
{
uint8 x_599; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_599 = 0;
return x_599;
}
}
}
default:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 12:
{
uint8 x_601; 
x_601 = 1;
return x_601;
}
default:
{
uint8 x_603; 
lean::dec(x_2);
x_603 = 0;
return x_603;
}
}
}
}
}
}
uint8 l_Lean_IR_Alts_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_10; obj* x_12; obj* x_15; obj* x_17; uint8 x_21; 
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
lean::inc(x_0);
x_21 = l_Lean_IR_Alt_alphaEqv___main(x_0, x_10, x_15);
if (x_21 == 0)
{
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_12);
return x_21;
}
else
{
x_1 = x_12;
x_2 = x_17;
goto _start;
}
}
}
}
}
uint8 l_Lean_IR_Alt_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_2) == 0)
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
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_10);
return x_13;
}
else
{
uint8 x_19; 
x_19 = l_Lean_IR_Fnbody_alphaEqv___main(x_0, x_5, x_10);
return x_19;
}
}
else
{
uint8 x_23; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_23 = 0;
return x_23;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_27; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_27 = 0;
return x_27;
}
else
{
obj* x_28; obj* x_31; uint8 x_34; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
lean::dec(x_2);
x_34 = l_Lean_IR_Fnbody_alphaEqv___main(x_0, x_28, x_31);
return x_34;
}
}
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
obj* l_Lean_IR_Alts_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Alts_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_IR_Alt_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Alt_alphaEqv___main(x_0, x_1, x_2);
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
uint8 l_Lean_IR_Alts_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Alts_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Alts_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Alts_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_Alt_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Alt_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Alt_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Alt_alphaEqv(x_0, x_1, x_2);
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
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_0, x_4);
return x_5;
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
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
x_5 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_0, x_4);
x_6 = lean::apply_2(x_1, x_5, x_3);
return x_6;
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
obj* x_2; obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_0, x_7, x_10);
x_0 = x_11;
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
obj* x_3; uint8 x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_NameSet_contains(x_1, x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_3, x_7);
return x_8;
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
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::box(0);
x_15 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_7, x_14);
x_16 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_9, x_1, x_15);
return x_16;
}
else
{
obj* x_18; 
lean::dec(x_7);
x_18 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_9, x_1, x_2);
return x_18;
}
}
case 3:
{
obj* x_19; uint8 x_22; 
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_Lean_NameSet_contains(x_1, x_19);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(0);
x_24 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_19, x_23);
return x_24;
}
else
{
lean::dec(x_19);
return x_2;
}
}
case 4:
{
obj* x_26; uint8 x_29; 
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
lean::dec(x_0);
x_29 = l_Lean_NameSet_contains(x_1, x_26);
if (x_29 == 0)
{
obj* x_30; obj* x_31; 
x_30 = lean::box(0);
x_31 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_26, x_30);
return x_31;
}
else
{
lean::dec(x_26);
return x_2;
}
}
case 5:
{
obj* x_33; uint8 x_36; 
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
lean::dec(x_0);
x_36 = l_Lean_NameSet_contains(x_1, x_33);
if (x_36 == 0)
{
obj* x_37; obj* x_38; 
x_37 = lean::box(0);
x_38 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_33, x_37);
return x_38;
}
else
{
lean::dec(x_33);
return x_2;
}
}
case 6:
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_0, 1);
lean::inc(x_40);
lean::dec(x_0);
x_43 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_40, x_1, x_2);
return x_43;
}
case 7:
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_0, 1);
lean::inc(x_44);
lean::dec(x_0);
x_47 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_44, x_1, x_2);
return x_47;
}
case 8:
{
obj* x_48; obj* x_50; uint8 x_54; 
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_0, 1);
lean::inc(x_50);
lean::dec(x_0);
lean::inc(x_1);
x_54 = l_Lean_NameSet_contains(x_1, x_48);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::box(0);
x_56 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_48, x_55);
x_57 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_50, x_1, x_56);
return x_57;
}
else
{
obj* x_59; 
lean::dec(x_48);
x_59 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_50, x_1, x_2);
return x_59;
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
obj* x_62; uint8 x_65; 
x_62 = lean::cnstr_get(x_0, 0);
lean::inc(x_62);
lean::dec(x_0);
x_65 = l_Lean_NameSet_contains(x_1, x_62);
if (x_65 == 0)
{
obj* x_66; obj* x_67; 
x_66 = lean::box(0);
x_67 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_62, x_66);
return x_67;
}
else
{
lean::dec(x_62);
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
obj* l___private_init_lean_compiler_ir_9__collectFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
x_11 = l___private_init_lean_compiler_ir_8__collectExpr___main(x_5, x_1, x_2);
x_12 = lean::box(0);
x_13 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_1, x_3, x_12);
x_0 = x_7;
x_1 = x_13;
x_2 = x_11;
goto _start;
}
case 1:
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 3);
lean::inc(x_21);
lean::dec(x_0);
lean::inc(x_1);
x_25 = l_List_foldl___main___at_Lean_IR_insertParams___spec__1(x_1, x_17);
x_26 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_19, x_25, x_2);
x_27 = lean::box(0);
x_28 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_1, x_15, x_27);
x_0 = x_21;
x_1 = x_28;
x_2 = x_26;
goto _start;
}
case 2:
{
obj* x_30; obj* x_32; obj* x_34; uint8 x_38; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 2);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 3);
lean::inc(x_34);
lean::dec(x_0);
lean::inc(x_1);
x_38 = l_Lean_NameSet_contains(x_1, x_30);
lean::inc(x_1);
x_40 = l_Lean_NameSet_contains(x_1, x_32);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::box(0);
x_42 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_30, x_41);
if (x_40 == 0)
{
obj* x_43; 
x_43 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_42, x_32, x_41);
x_0 = x_34;
x_2 = x_43;
goto _start;
}
else
{
lean::dec(x_32);
x_0 = x_34;
x_2 = x_42;
goto _start;
}
}
else
{
lean::dec(x_30);
if (x_40 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::box(0);
x_49 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_32, x_48);
x_0 = x_34;
x_2 = x_49;
goto _start;
}
else
{
lean::dec(x_32);
x_0 = x_34;
goto _start;
}
}
}
case 3:
{
obj* x_53; obj* x_55; obj* x_57; uint8 x_61; uint8 x_63; 
x_53 = lean::cnstr_get(x_0, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_0, 2);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_0, 3);
lean::inc(x_57);
lean::dec(x_0);
lean::inc(x_1);
x_61 = l_Lean_NameSet_contains(x_1, x_53);
lean::inc(x_1);
x_63 = l_Lean_NameSet_contains(x_1, x_55);
if (x_61 == 0)
{
obj* x_64; obj* x_65; 
x_64 = lean::box(0);
x_65 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_53, x_64);
if (x_63 == 0)
{
obj* x_66; 
x_66 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_65, x_55, x_64);
x_0 = x_57;
x_2 = x_66;
goto _start;
}
else
{
lean::dec(x_55);
x_0 = x_57;
x_2 = x_65;
goto _start;
}
}
else
{
lean::dec(x_53);
if (x_63 == 0)
{
obj* x_71; obj* x_72; 
x_71 = lean::box(0);
x_72 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_55, x_71);
x_0 = x_57;
x_2 = x_72;
goto _start;
}
else
{
lean::dec(x_55);
x_0 = x_57;
goto _start;
}
}
}
case 4:
{
obj* x_76; obj* x_78; obj* x_80; uint8 x_84; uint8 x_86; 
x_76 = lean::cnstr_get(x_0, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_0, 3);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_0, 4);
lean::inc(x_80);
lean::dec(x_0);
lean::inc(x_1);
x_84 = l_Lean_NameSet_contains(x_1, x_76);
lean::inc(x_1);
x_86 = l_Lean_NameSet_contains(x_1, x_78);
if (x_84 == 0)
{
obj* x_87; obj* x_88; 
x_87 = lean::box(0);
x_88 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_76, x_87);
if (x_86 == 0)
{
obj* x_89; 
x_89 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_88, x_78, x_87);
x_0 = x_80;
x_2 = x_89;
goto _start;
}
else
{
lean::dec(x_78);
x_0 = x_80;
x_2 = x_88;
goto _start;
}
}
else
{
lean::dec(x_76);
if (x_86 == 0)
{
obj* x_94; obj* x_95; 
x_94 = lean::box(0);
x_95 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_78, x_94);
x_0 = x_80;
x_2 = x_95;
goto _start;
}
else
{
lean::dec(x_78);
x_0 = x_80;
goto _start;
}
}
}
case 8:
{
obj* x_99; 
x_99 = lean::cnstr_get(x_0, 1);
lean::inc(x_99);
lean::dec(x_0);
x_0 = x_99;
goto _start;
}
case 9:
{
obj* x_103; obj* x_105; uint8 x_109; 
x_103 = lean::cnstr_get(x_0, 1);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_0, 2);
lean::inc(x_105);
lean::dec(x_0);
lean::inc(x_1);
x_109 = l_Lean_NameSet_contains(x_1, x_103);
if (x_109 == 0)
{
obj* x_110; obj* x_111; obj* x_112; 
x_110 = lean::box(0);
x_111 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_103, x_110);
x_112 = l___private_init_lean_compiler_ir_9__collectAlts___main(x_105, x_1, x_111);
return x_112;
}
else
{
obj* x_114; 
lean::dec(x_103);
x_114 = l___private_init_lean_compiler_ir_9__collectAlts___main(x_105, x_1, x_2);
return x_114;
}
}
case 10:
{
obj* x_115; uint8 x_118; 
x_115 = lean::cnstr_get(x_0, 0);
lean::inc(x_115);
lean::dec(x_0);
x_118 = l_Lean_NameSet_contains(x_1, x_115);
if (x_118 == 0)
{
obj* x_119; obj* x_120; 
x_119 = lean::box(0);
x_120 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_115, x_119);
return x_120;
}
else
{
lean::dec(x_115);
return x_2;
}
}
case 11:
{
obj* x_122; obj* x_124; uint8 x_128; 
x_122 = lean::cnstr_get(x_0, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_0, 1);
lean::inc(x_124);
lean::dec(x_0);
lean::inc(x_1);
x_128 = l_Lean_NameSet_contains(x_1, x_122);
if (x_128 == 0)
{
obj* x_129; obj* x_130; obj* x_131; 
x_129 = lean::box(0);
x_130 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_122, x_129);
x_131 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_124, x_1, x_130);
return x_131;
}
else
{
obj* x_133; 
lean::dec(x_122);
x_133 = l___private_init_lean_compiler_ir_7__collectArgs___main(x_124, x_1, x_2);
return x_133;
}
}
case 12:
{
lean::dec(x_1);
return x_2;
}
default:
{
obj* x_135; obj* x_137; uint8 x_141; 
x_135 = lean::cnstr_get(x_0, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_0, 2);
lean::inc(x_137);
lean::dec(x_0);
lean::inc(x_1);
x_141 = l_Lean_NameSet_contains(x_1, x_135);
if (x_141 == 0)
{
obj* x_142; obj* x_143; 
x_142 = lean::box(0);
x_143 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_2, x_135, x_142);
x_0 = x_137;
x_2 = x_143;
goto _start;
}
else
{
lean::dec(x_135);
x_0 = x_137;
goto _start;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_9__collectAlts___main(obj* x_0, obj* x_1, obj* x_2) {
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
x_10 = l___private_init_lean_compiler_ir_9__collectAlt___main(x_4, x_1, x_2);
x_0 = x_6;
x_2 = x_10;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_9__collectAlt___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_3, x_1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l___private_init_lean_compiler_ir_9__collectFnBody___main(x_7, x_1, x_2);
return x_10;
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
obj* l___private_init_lean_compiler_ir_9__collectAlts(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_9__collectAlts___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_9__collectAlt(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_9__collectAlt___main(x_0, x_1, x_2);
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
