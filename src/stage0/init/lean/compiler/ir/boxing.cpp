// Lean compiler output
// Module: init.lean.compiler.ir.boxing
// Imports: init.control.estate init.control.reader init.lean.compiler.ir.basic
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
obj* l_Lean_IR_ExplicitBoxing_visitFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(obj*, obj*);
extern obj* l_Array_empty___closed__1;
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_ExplicitBoxing_getResultType(obj*, obj*);
obj* l_Lean_IR_Context_addJP(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withJDecl(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(obj*, obj*);
uint8 l_Lean_IR_Decl_resultType___main(obj*);
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Context_getJPParams(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withVDecl(obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withJDecl___boxed(obj*);
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(obj*);
obj* l_Lean_IR_ExplicitBoxing_mkCast___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_ExplicitBoxing_getResultType___boxed(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(obj*);
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(obj*, uint8, obj*, uint8, obj*, obj*, obj*);
uint8 l_Lean_IR_ExplicitBoxing_eqvTypes(uint8, uint8);
obj* l_Lean_IR_ExplicitBoxing_getVarType(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_isScalar(obj*);
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_paramInh;
obj* l_Array_miterateAux___main___at_Lean_IR_Context_addParams___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Context_getType(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkFresh(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1___closed__1;
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_params___main(obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withParams___boxed(obj*);
obj* l_Lean_IR_ExplicitBoxing_getDecl(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getEnv(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getVarType___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getJPParams(obj*, obj*, obj*);
obj* l_Lean_IR_Context_addLocal(obj*, obj*, uint8, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_ExplicitBoxing_getScrutineeType(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_visitFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getCtx(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withParams(obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkCast(obj*, uint8);
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_isScalar___main(uint8);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::nat_dec_lt(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::array_fget(x_0, x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_11; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = l_Lean_IR_CtorInfo_isScalar(x_8);
lean::dec(x_8);
if (x_11 == 0)
{
uint8 x_14; 
lean::dec(x_1);
x_14 = 1;
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_1, x_15);
lean::dec(x_1);
x_1 = x_16;
goto _start;
}
}
else
{
uint8 x_21; 
lean::dec(x_7);
lean::dec(x_1);
x_21 = 1;
return x_21;
}
}
}
}
uint8 l_Lean_IR_ExplicitBoxing_getScrutineeType(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
uint8 x_5; 
lean::dec(x_1);
x_5 = 7;
return x_5;
}
else
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_0, x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(256ul);
x_9 = lean::nat_dec_lt(x_1, x_8);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(65536ul);
x_11 = lean::nat_dec_lt(x_1, x_10);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::mk_nat_obj(4294967296ul);
x_13 = lean::nat_dec_lt(x_1, x_12);
lean::dec(x_1);
if (x_13 == 0)
{
uint8 x_15; 
x_15 = 7;
return x_15;
}
else
{
uint8 x_16; 
x_16 = 3;
return x_16;
}
}
else
{
uint8 x_18; 
lean::dec(x_1);
x_18 = 2;
return x_18;
}
}
else
{
uint8 x_20; 
lean::dec(x_1);
x_20 = 1;
return x_20;
}
}
else
{
uint8 x_22; 
lean::dec(x_1);
x_22 = 7;
return x_22;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_ExplicitBoxing_eqvTypes(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; uint8 x_3; 
x_2 = l_Lean_IR_IRType_isScalar___main(x_0);
x_3 = l_Lean_IR_IRType_isScalar___main(x_1);
if (x_2 == 0)
{
if (x_3 == 0)
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
if (x_3 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = l_Lean_IR_IRType_beq___main(x_0, x_1);
return x_7;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1ul);
x_2 = lean::nat_add(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkFresh(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_mkFresh___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_ExplicitBoxing_mkFresh(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_getEnv(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_getCtx(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_getResultType(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_getResultType___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_getResultType(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_getVarType(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_3 = l_Lean_IR_ExplicitBoxing_getCtx(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_Context_getType(x_4, x_0);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; obj* x_11; obj* x_12; 
x_10 = 7;
x_11 = lean::box(x_10);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_6);
return x_16;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_getVarType___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getVarType(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_getJPParams(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_3 = l_Lean_IR_ExplicitBoxing_getCtx(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_Context_getJPParams(x_4, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
x_10 = l_Array_empty___closed__1;
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_6);
return x_15;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getJPParams(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_getDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*2);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::mk_nat_obj(0ul);
x_11 = l_Array_miterateAux___main___at_Lean_IR_Context_addParams___spec__1(x_0, x_0, x_10, x_4);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_7);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_6);
x_13 = x_12;
x_14 = lean::apply_2(x_1, x_13, x_3);
return x_14;
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_withParams___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_ExplicitBoxing_withParams(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_4, 0);
x_8 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*2);
x_9 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_6);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = l_Lean_IR_Context_addLocal(x_6, x_0, x_1, x_2);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_8);
x_14 = x_13;
x_15 = lean::apply_2(x_3, x_14, x_5);
return x_15;
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_IR_ExplicitBoxing_withVDecl___rarg(x_0, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_ExplicitBoxing_withVDecl(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_4, 0);
x_8 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*2);
x_9 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_6);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = l_Lean_IR_Context_addJP(x_6, x_0, x_1, x_2);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_8);
x_14 = x_13;
x_15 = lean::apply_2(x_3, x_14, x_5);
return x_15;
}
}
obj* l_Lean_IR_ExplicitBoxing_withJDecl(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_withJDecl___rarg), 6, 0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_withJDecl___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_ExplicitBoxing_withJDecl(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkCast(obj* x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_IRType_isScalar___main(x_1);
if (x_2 == 0)
{
obj* x_3; 
x_3 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1, x_1);
x_5 = x_4;
return x_5;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_mkCast___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_Lean_IR_ExplicitBoxing_mkCast(x_0, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; uint8 x_12; uint8 x_13; 
lean::inc(x_3);
x_6 = l_Lean_IR_ExplicitBoxing_getVarType(x_0, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::unbox(x_7);
x_13 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_12, x_1);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_14 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_9);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_Lean_IR_ExplicitBoxing_mkCast(x_0, x_12);
lean::inc(x_15);
x_22 = lean::apply_3(x_2, x_15, x_3, x_17);
x_23 = lean::cnstr_get(x_22, 0);
x_25 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_27 = x_22;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_22);
 x_27 = lean::box(0);
}
x_28 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_20);
lean::cnstr_set(x_28, 2, x_23);
lean::cnstr_set_scalar(x_28, sizeof(void*)*3, x_1);
x_29 = x_28;
if (lean::is_scalar(x_27)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_27;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_25);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::apply_3(x_2, x_0, x_3, x_9);
return x_31;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_Lean_IR_ExplicitBoxing_castVarIfNeeded(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; uint8 x_15; uint8 x_16; 
x_5 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
lean::inc(x_3);
x_9 = l_Lean_IR_ExplicitBoxing_getVarType(x_5, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::unbox(x_10);
x_16 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_15, x_1);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_20; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_17 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_12);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_Lean_IR_ExplicitBoxing_mkCast(x_5, x_15);
lean::inc(x_18);
if (lean::is_scalar(x_7)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_7;
}
lean::cnstr_set(x_25, 0, x_18);
x_26 = lean::apply_3(x_2, x_25, x_3, x_20);
x_27 = lean::cnstr_get(x_26, 0);
x_29 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_31 = x_26;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_26);
 x_31 = lean::box(0);
}
x_32 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_32, 0, x_18);
lean::cnstr_set(x_32, 1, x_23);
lean::cnstr_set(x_32, 2, x_27);
lean::cnstr_set_scalar(x_32, sizeof(void*)*3, x_1);
x_33 = x_32;
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_29);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
if (lean::is_scalar(x_7)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_7;
}
lean::cnstr_set(x_35, 0, x_5);
x_36 = lean::apply_3(x_2, x_35, x_3, x_12);
return x_36;
}
}
else
{
obj* x_37; 
x_37 = lean::apply_3(x_2, x_0, x_3, x_4);
return x_37;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_13; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; uint8 x_19; 
x_14 = lean::array_fget(x_2, x_3);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_3, x_15);
lean::inc(x_1);
x_18 = lean::apply_1(x_1, x_3);
x_19 = lean::unbox(x_18);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_28; obj* x_29; obj* x_31; obj* x_33; uint8 x_34; uint8 x_35; 
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_4, 1);
lean::inc(x_22);
lean::dec(x_4);
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
lean::inc(x_5);
x_28 = l_Lean_IR_ExplicitBoxing_getVarType(x_25, x_5, x_6);
x_29 = lean::cnstr_get(x_28, 0);
x_31 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 lean::cnstr_set(x_28, 1, lean::box(0));
 x_33 = x_28;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_28);
 x_33 = lean::box(0);
}
x_34 = lean::unbox(x_29);
x_35 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_34, x_19);
if (x_35 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_33);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_37 = x_14;
} else {
 lean::dec(x_14);
 x_37 = lean::box(0);
}
x_38 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_31);
x_39 = lean::cnstr_get(x_38, 0);
x_41 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 x_43 = x_38;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_38);
 x_43 = lean::box(0);
}
x_44 = l_Lean_IR_ExplicitBoxing_mkCast(x_25, x_34);
x_45 = lean::box(12);
lean::inc(x_39);
x_47 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_47, 0, x_39);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*3, x_19);
x_48 = x_47;
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_39);
x_50 = lean::array_push(x_20, x_49);
x_51 = lean::array_push(x_22, x_48);
if (lean::is_scalar(x_43)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_43;
}
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_51);
x_3 = x_16;
x_4 = x_52;
x_6 = x_41;
goto _start;
}
else
{
obj* x_55; obj* x_56; 
lean::dec(x_25);
x_55 = lean::array_push(x_20, x_14);
if (lean::is_scalar(x_33)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_33;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_22);
x_3 = x_16;
x_4 = x_56;
x_6 = x_31;
goto _start;
}
}
else
{
obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
x_58 = lean::cnstr_get(x_4, 0);
x_60 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_62 = x_4;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_4);
 x_62 = lean::box(0);
}
x_63 = lean::array_push(x_58, x_14);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_60);
x_3 = x_16;
x_4 = x_64;
goto _start;
}
}
}
}
obj* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_empty_array(x_0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_0, x_1, x_0, x_4, x_5, x_2, x_3);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_3);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_19; 
x_13 = lean::array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_3, x_14);
x_16 = l_Lean_IR_paramInh;
x_17 = lean::array_get(x_16, x_0, x_3);
lean::dec(x_3);
x_19 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1 + 1);
lean::dec(x_17);
if (lean::obj_tag(x_13) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; uint8 x_35; uint8 x_36; 
x_21 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_4, 1);
lean::inc(x_23);
lean::dec(x_4);
x_26 = lean::cnstr_get(x_13, 0);
lean::inc(x_26);
lean::inc(x_5);
x_29 = l_Lean_IR_ExplicitBoxing_getVarType(x_26, x_5, x_6);
x_30 = lean::cnstr_get(x_29, 0);
x_32 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_set(x_29, 0, lean::box(0));
 lean::cnstr_set(x_29, 1, lean::box(0));
 x_34 = x_29;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_29);
 x_34 = lean::box(0);
}
x_35 = lean::unbox(x_30);
x_36 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_35, x_19);
if (x_36 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_34);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_38 = x_13;
} else {
 lean::dec(x_13);
 x_38 = lean::box(0);
}
x_39 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_32);
x_40 = lean::cnstr_get(x_39, 0);
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = l_Lean_IR_ExplicitBoxing_mkCast(x_26, x_35);
x_46 = lean::box(12);
lean::inc(x_40);
x_48 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_48, 0, x_40);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_46);
lean::cnstr_set_scalar(x_48, sizeof(void*)*3, x_19);
x_49 = x_48;
if (lean::is_scalar(x_38)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_38;
}
lean::cnstr_set(x_50, 0, x_40);
x_51 = lean::array_push(x_21, x_50);
x_52 = lean::array_push(x_23, x_49);
if (lean::is_scalar(x_44)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_44;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_3 = x_15;
x_4 = x_53;
x_6 = x_42;
goto _start;
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_26);
x_56 = lean::array_push(x_21, x_13);
if (lean::is_scalar(x_34)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_34;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_23);
x_3 = x_15;
x_4 = x_57;
x_6 = x_32;
goto _start;
}
}
else
{
obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
x_59 = lean::cnstr_get(x_4, 0);
x_61 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_63 = x_4;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_4);
 x_63 = lean::box(0);
}
x_64 = lean::array_push(x_59, x_13);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
x_3 = x_15;
x_4 = x_65;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_0, x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::inc(x_3);
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(x_1, x_0, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::apply_3(x_2, x_12, x_3, x_9);
x_18 = lean::cnstr_get(x_17, 0);
x_20 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_22 = x_17;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
x_23 = l_Lean_IR_reshape(x_14, x_18);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_20);
return x_24;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_11; 
lean::dec(x_4);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_5);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::array_fget(x_1, x_2);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_27; obj* x_29; uint8 x_30; uint8 x_31; uint8 x_32; 
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_12, 0);
lean::inc(x_21);
lean::inc(x_4);
x_24 = l_Lean_IR_ExplicitBoxing_getVarType(x_21, x_4, x_5);
x_25 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 lean::cnstr_set(x_24, 1, lean::box(0));
 x_29 = x_24;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = 7;
x_31 = lean::unbox(x_25);
x_32 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_31, x_30);
if (x_32 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_29);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_34 = x_12;
} else {
 lean::dec(x_12);
 x_34 = lean::box(0);
}
x_35 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_27);
x_36 = lean::cnstr_get(x_35, 0);
x_38 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_40 = x_35;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_35);
 x_40 = lean::box(0);
}
x_41 = l_Lean_IR_ExplicitBoxing_mkCast(x_21, x_31);
x_42 = lean::box(12);
lean::inc(x_36);
x_44 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_44, 0, x_36);
lean::cnstr_set(x_44, 1, x_41);
lean::cnstr_set(x_44, 2, x_42);
lean::cnstr_set_scalar(x_44, sizeof(void*)*3, x_30);
x_45 = x_44;
if (lean::is_scalar(x_34)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_34;
}
lean::cnstr_set(x_46, 0, x_36);
x_47 = lean::array_push(x_16, x_46);
x_48 = lean::array_push(x_18, x_45);
if (lean::is_scalar(x_40)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_40;
}
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
x_2 = x_14;
x_3 = x_49;
x_5 = x_38;
goto _start;
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_21);
x_52 = lean::array_push(x_16, x_12);
if (lean::is_scalar(x_29)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_29;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_18);
x_2 = x_14;
x_3 = x_53;
x_5 = x_27;
goto _start;
}
}
else
{
obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
x_55 = lean::cnstr_get(x_3, 0);
x_57 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_59 = x_3;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_3);
 x_59 = lean::box(0);
}
x_60 = lean::array_push(x_55, x_12);
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_59;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_57);
x_2 = x_14;
x_3 = x_61;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_5 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_0, x_0, x_3, x_4, x_1, x_2);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::inc(x_2);
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::apply_3(x_1, x_11, x_2, x_8);
x_17 = lean::cnstr_get(x_16, 0);
x_19 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_21 = x_16;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_16);
 x_21 = lean::box(0);
}
x_22 = l_Lean_IR_reshape(x_13, x_17);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_Lean_IR_IRType_isScalar___main(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set_scalar(x_7, sizeof(void*)*3, x_1);
x_8 = x_7;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_10 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_5);
x_11 = lean::cnstr_get(x_10, 0);
x_13 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_15 = x_10;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
lean::inc(x_11);
x_17 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_17, 0, x_11);
x_18 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_3);
lean::cnstr_set_scalar(x_18, sizeof(void*)*3, x_1);
x_19 = x_18;
x_20 = 7;
x_21 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_20);
x_22 = x_21;
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_13);
return x_23;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_0, x_6, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(obj* x_0, uint8 x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_1, x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_8 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_6);
x_9 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_13 = x_8;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
lean::inc(x_9);
x_15 = l_Lean_IR_ExplicitBoxing_mkCast(x_9, x_3);
x_16 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set(x_16, 2, x_4);
lean::cnstr_set_scalar(x_16, sizeof(void*)*3, x_1);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_2);
lean::cnstr_set(x_18, 2, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*3, x_3);
x_19 = x_18;
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_11);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_4);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_1);
x_22 = x_21;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_6);
return x_23;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_1);
x_8 = lean::unbox(x_3);
x_9 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_0, x_7, x_2, x_8, x_4, x_5, x_6);
lean::dec(x_5);
return x_9;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_3);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_19; 
x_13 = lean::array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_3, x_14);
x_16 = l_Lean_IR_paramInh;
x_17 = lean::array_get(x_16, x_0, x_3);
lean::dec(x_3);
x_19 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1 + 1);
lean::dec(x_17);
if (lean::obj_tag(x_13) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; uint8 x_35; uint8 x_36; 
x_21 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_4, 1);
lean::inc(x_23);
lean::dec(x_4);
x_26 = lean::cnstr_get(x_13, 0);
lean::inc(x_26);
lean::inc(x_5);
x_29 = l_Lean_IR_ExplicitBoxing_getVarType(x_26, x_5, x_6);
x_30 = lean::cnstr_get(x_29, 0);
x_32 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_set(x_29, 0, lean::box(0));
 lean::cnstr_set(x_29, 1, lean::box(0));
 x_34 = x_29;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_29);
 x_34 = lean::box(0);
}
x_35 = lean::unbox(x_30);
x_36 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_35, x_19);
if (x_36 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_34);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_38 = x_13;
} else {
 lean::dec(x_13);
 x_38 = lean::box(0);
}
x_39 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_32);
x_40 = lean::cnstr_get(x_39, 0);
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = l_Lean_IR_ExplicitBoxing_mkCast(x_26, x_35);
x_46 = lean::box(12);
lean::inc(x_40);
x_48 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_48, 0, x_40);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_46);
lean::cnstr_set_scalar(x_48, sizeof(void*)*3, x_19);
x_49 = x_48;
if (lean::is_scalar(x_38)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_38;
}
lean::cnstr_set(x_50, 0, x_40);
x_51 = lean::array_push(x_21, x_50);
x_52 = lean::array_push(x_23, x_49);
if (lean::is_scalar(x_44)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_44;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_3 = x_15;
x_4 = x_53;
x_6 = x_42;
goto _start;
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_26);
x_56 = lean::array_push(x_21, x_13);
if (lean::is_scalar(x_34)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_34;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_23);
x_3 = x_15;
x_4 = x_57;
x_6 = x_32;
goto _start;
}
}
else
{
obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
x_59 = lean::cnstr_get(x_4, 0);
x_61 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_63 = x_4;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_4);
 x_63 = lean::box(0);
}
x_64 = lean::array_push(x_59, x_13);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
x_3 = x_15;
x_4 = x_65;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_0, x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_6; obj* x_8; obj* x_10; uint8 x_11; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = l_Lean_IR_CtorInfo_isScalar(x_6);
if (x_11 == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_12 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_8, x_4, x_5);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_23 = x_14;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_14);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_10;
}
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_19);
x_25 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_3);
lean::cnstr_set_scalar(x_25, sizeof(void*)*3, x_1);
x_26 = x_25;
x_27 = l_Lean_IR_reshape(x_21, x_26);
if (lean::is_scalar(x_23)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_23;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_16);
return x_28;
}
else
{
uint8 x_29; 
x_29 = l_Lean_IR_IRType_isScalar___main(x_1);
if (x_29 == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_30 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_8, x_4, x_5);
lean::dec(x_8);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_30, 1);
lean::inc(x_34);
lean::dec(x_30);
x_37 = lean::cnstr_get(x_32, 0);
x_39 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_10;
}
lean::cnstr_set(x_42, 0, x_6);
lean::cnstr_set(x_42, 1, x_37);
x_43 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_43, 0, x_0);
lean::cnstr_set(x_43, 1, x_42);
lean::cnstr_set(x_43, 2, x_3);
lean::cnstr_set_scalar(x_43, sizeof(void*)*3, x_1);
x_44 = x_43;
x_45 = l_Lean_IR_reshape(x_39, x_44);
if (lean::is_scalar(x_41)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_41;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_34);
return x_46;
}
else
{
obj* x_50; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_4);
x_50 = lean::cnstr_get(x_6, 1);
lean::inc(x_50);
lean::dec(x_6);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
x_54 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_55, 0, x_0);
lean::cnstr_set(x_55, 1, x_54);
lean::cnstr_set(x_55, 2, x_3);
lean::cnstr_set_scalar(x_55, sizeof(void*)*3, x_1);
x_56 = x_55;
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_5);
return x_57;
}
}
}
case 2:
{
obj* x_58; obj* x_60; uint8 x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_70; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_58 = lean::cnstr_get(x_2, 0);
x_60 = lean::cnstr_get(x_2, 1);
x_62 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_63 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 x_65 = x_2;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::inc(x_63);
 lean::dec(x_2);
 x_65 = lean::box(0);
}
x_66 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_63, x_4, x_5);
lean::dec(x_63);
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
lean::dec(x_66);
x_73 = lean::cnstr_get(x_68, 0);
x_75 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 x_77 = x_68;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_68);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_78 = lean::alloc_cnstr(2, 3, 1);
} else {
 x_78 = x_65;
}
lean::cnstr_set(x_78, 0, x_58);
lean::cnstr_set(x_78, 1, x_60);
lean::cnstr_set(x_78, 2, x_73);
lean::cnstr_set_scalar(x_78, sizeof(void*)*3, x_62);
x_79 = x_78;
x_80 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_80, 0, x_0);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set(x_80, 2, x_3);
lean::cnstr_set_scalar(x_80, sizeof(void*)*3, x_1);
x_81 = x_80;
x_82 = l_Lean_IR_reshape(x_75, x_81);
if (lean::is_scalar(x_77)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_77;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_70);
return x_83;
}
case 6:
{
obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; obj* x_94; obj* x_97; obj* x_99; obj* x_102; obj* x_104; obj* x_107; obj* x_109; obj* x_112; uint8 x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_122; obj* x_123; 
x_84 = lean::cnstr_get(x_2, 0);
x_86 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_88 = x_2;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_2);
 x_88 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_84);
x_91 = l_Lean_IR_ExplicitBoxing_getDecl(x_84, x_4, x_5);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
x_97 = l_Lean_IR_Decl_params___main(x_92);
lean::inc(x_4);
x_99 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_97, x_86, x_4, x_94);
lean::dec(x_86);
lean::dec(x_97);
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
lean::dec(x_99);
x_107 = lean::cnstr_get(x_102, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_102, 1);
lean::inc(x_109);
lean::dec(x_102);
if (lean::is_scalar(x_88)) {
 x_112 = lean::alloc_cnstr(6, 2, 0);
} else {
 x_112 = x_88;
}
lean::cnstr_set(x_112, 0, x_84);
lean::cnstr_set(x_112, 1, x_107);
x_113 = l_Lean_IR_Decl_resultType___main(x_92);
lean::dec(x_92);
x_115 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_0, x_1, x_112, x_113, x_3, x_4, x_104);
lean::dec(x_4);
x_117 = lean::cnstr_get(x_115, 0);
x_119 = lean::cnstr_get(x_115, 1);
if (lean::is_exclusive(x_115)) {
 x_121 = x_115;
} else {
 lean::inc(x_117);
 lean::inc(x_119);
 lean::dec(x_115);
 x_121 = lean::box(0);
}
x_122 = l_Lean_IR_reshape(x_109, x_117);
if (lean::is_scalar(x_121)) {
 x_123 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_123 = x_121;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_119);
return x_123;
}
case 7:
{
obj* x_124; obj* x_126; obj* x_128; obj* x_131; obj* x_132; obj* x_135; obj* x_137; obj* x_139; obj* x_142; obj* x_144; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_124 = lean::cnstr_get(x_2, 0);
x_126 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_128 = x_2;
} else {
 lean::inc(x_124);
 lean::inc(x_126);
 lean::dec(x_2);
 x_128 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_124);
x_131 = l_Lean_IR_ExplicitBoxing_getDecl(x_124, x_4, x_5);
x_132 = lean::cnstr_get(x_131, 1);
lean::inc(x_132);
lean::dec(x_131);
x_135 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_126, x_4, x_132);
lean::dec(x_126);
x_137 = lean::cnstr_get(x_135, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_135, 1);
lean::inc(x_139);
lean::dec(x_135);
x_142 = lean::cnstr_get(x_137, 0);
x_144 = lean::cnstr_get(x_137, 1);
if (lean::is_exclusive(x_137)) {
 x_146 = x_137;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::dec(x_137);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_147 = lean::alloc_cnstr(7, 2, 0);
} else {
 x_147 = x_128;
}
lean::cnstr_set(x_147, 0, x_124);
lean::cnstr_set(x_147, 1, x_142);
x_148 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_148, 0, x_0);
lean::cnstr_set(x_148, 1, x_147);
lean::cnstr_set(x_148, 2, x_3);
lean::cnstr_set_scalar(x_148, sizeof(void*)*3, x_1);
x_149 = x_148;
x_150 = l_Lean_IR_reshape(x_144, x_149);
if (lean::is_scalar(x_146)) {
 x_151 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_151 = x_146;
}
lean::cnstr_set(x_151, 0, x_150);
lean::cnstr_set(x_151, 1, x_139);
return x_151;
}
case 8:
{
obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_165; obj* x_167; obj* x_170; obj* x_171; obj* x_173; obj* x_175; obj* x_177; obj* x_178; obj* x_179; 
x_152 = lean::cnstr_get(x_2, 0);
x_154 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_156 = x_2;
} else {
 lean::inc(x_152);
 lean::inc(x_154);
 lean::dec(x_2);
 x_156 = lean::box(0);
}
lean::inc(x_4);
x_158 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_154, x_4, x_5);
lean::dec(x_154);
x_160 = lean::cnstr_get(x_158, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_158, 1);
lean::inc(x_162);
lean::dec(x_158);
x_165 = lean::cnstr_get(x_160, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_160, 1);
lean::inc(x_167);
lean::dec(x_160);
if (lean::is_scalar(x_156)) {
 x_170 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_170 = x_156;
}
lean::cnstr_set(x_170, 0, x_152);
lean::cnstr_set(x_170, 1, x_165);
x_171 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_0, x_1, x_170, x_3, x_4, x_162);
lean::dec(x_4);
x_173 = lean::cnstr_get(x_171, 0);
x_175 = lean::cnstr_get(x_171, 1);
if (lean::is_exclusive(x_171)) {
 x_177 = x_171;
} else {
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_171);
 x_177 = lean::box(0);
}
x_178 = l_Lean_IR_reshape(x_167, x_173);
if (lean::is_scalar(x_177)) {
 x_179 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_179 = x_177;
}
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_175);
return x_179;
}
default:
{
obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_4);
x_181 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_181, 0, x_0);
lean::cnstr_set(x_181, 1, x_2);
lean::cnstr_set(x_181, 2, x_3);
lean::cnstr_set_scalar(x_181, sizeof(void*)*3, x_1);
x_182 = x_181;
x_183 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_183, 0, x_182);
lean::cnstr_set(x_183, 1, x_5);
return x_183;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_0, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(12);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::array_fget(x_1, x_0);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1___closed__1;
x_12 = lean::array_fset(x_1, x_0, x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
lean::inc(x_2);
x_19 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_15, x_2, x_3);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_20);
x_26 = lean::mk_nat_obj(1ul);
x_27 = lean::nat_add(x_0, x_26);
x_28 = lean::array_fset(x_12, x_0, x_25);
lean::dec(x_0);
x_0 = x_27;
x_1 = x_28;
x_3 = x_22;
goto _start;
}
else
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_31 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_33 = x_10;
} else {
 lean::inc(x_31);
 lean::dec(x_10);
 x_33 = lean::box(0);
}
lean::inc(x_2);
x_35 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_31, x_2, x_3);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
if (lean::is_scalar(x_33)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_33;
}
lean::cnstr_set(x_41, 0, x_36);
x_42 = lean::mk_nat_obj(1ul);
x_43 = lean::nat_add(x_0, x_42);
x_44 = lean::array_fset(x_12, x_0, x_41);
lean::dec(x_0);
x_0 = x_43;
x_1 = x_44;
x_3 = x_38;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_3);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_19; 
x_13 = lean::array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_3, x_14);
x_16 = l_Lean_IR_paramInh;
x_17 = lean::array_get(x_16, x_0, x_3);
lean::dec(x_3);
x_19 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1 + 1);
lean::dec(x_17);
if (lean::obj_tag(x_13) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; uint8 x_35; uint8 x_36; 
x_21 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_4, 1);
lean::inc(x_23);
lean::dec(x_4);
x_26 = lean::cnstr_get(x_13, 0);
lean::inc(x_26);
lean::inc(x_5);
x_29 = l_Lean_IR_ExplicitBoxing_getVarType(x_26, x_5, x_6);
x_30 = lean::cnstr_get(x_29, 0);
x_32 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_set(x_29, 0, lean::box(0));
 lean::cnstr_set(x_29, 1, lean::box(0));
 x_34 = x_29;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_29);
 x_34 = lean::box(0);
}
x_35 = lean::unbox(x_30);
x_36 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_35, x_19);
if (x_36 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_34);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_38 = x_13;
} else {
 lean::dec(x_13);
 x_38 = lean::box(0);
}
x_39 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_32);
x_40 = lean::cnstr_get(x_39, 0);
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = l_Lean_IR_ExplicitBoxing_mkCast(x_26, x_35);
x_46 = lean::box(12);
lean::inc(x_40);
x_48 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_48, 0, x_40);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_46);
lean::cnstr_set_scalar(x_48, sizeof(void*)*3, x_19);
x_49 = x_48;
if (lean::is_scalar(x_38)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_38;
}
lean::cnstr_set(x_50, 0, x_40);
x_51 = lean::array_push(x_21, x_50);
x_52 = lean::array_push(x_23, x_49);
if (lean::is_scalar(x_44)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_44;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_3 = x_15;
x_4 = x_53;
x_6 = x_42;
goto _start;
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_26);
x_56 = lean::array_push(x_21, x_13);
if (lean::is_scalar(x_34)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_34;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_23);
x_3 = x_15;
x_4 = x_57;
x_6 = x_32;
goto _start;
}
}
else
{
obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
x_59 = lean::cnstr_get(x_4, 0);
x_61 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_63 = x_4;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_4);
 x_63 = lean::box(0);
}
x_64 = lean::array_push(x_59, x_13);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
x_3 = x_15;
x_4 = x_65;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_0, x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_11; uint8 x_13; obj* x_14; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_27; 
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::inc(x_6);
lean::inc(x_4);
x_18 = l_Lean_IR_Context_addLocal(x_11, x_4, x_3, x_6);
x_19 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_14);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_13);
x_20 = x_19;
x_21 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_8, x_20, x_2);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_4, x_3, x_6, x_22, x_1, x_24);
return x_27;
}
case 1:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_37; uint8 x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_1, 0);
x_39 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
x_40 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_42 = x_1;
} else {
 lean::inc(x_37);
 lean::inc(x_40);
 lean::dec(x_1);
 x_42 = lean::box(0);
}
x_43 = lean::mk_nat_obj(0ul);
lean::inc(x_37);
x_45 = l_Array_miterateAux___main___at_Lean_IR_Context_addParams___spec__1(x_30, x_30, x_43, x_37);
lean::inc(x_40);
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_39);
x_48 = x_47;
x_49 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_32, x_48, x_2);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
lean::inc(x_50);
lean::inc(x_30);
lean::inc(x_28);
x_58 = l_Lean_IR_Context_addJP(x_37, x_28, x_30, x_50);
x_59 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_40);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_39);
x_60 = x_59;
x_61 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_34, x_60, x_52);
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_67 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_67 = x_36;
}
lean::cnstr_set(x_67, 0, x_28);
lean::cnstr_set(x_67, 1, x_30);
lean::cnstr_set(x_67, 2, x_50);
lean::cnstr_set(x_67, 3, x_62);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
case 3:
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_85; obj* x_86; obj* x_88; obj* x_90; uint8 x_91; uint8 x_92; uint8 x_93; 
x_69 = lean::cnstr_get(x_0, 0);
x_71 = lean::cnstr_get(x_0, 1);
x_73 = lean::cnstr_get(x_0, 2);
x_75 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_77 = x_0;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_0);
 x_77 = lean::box(0);
}
lean::inc(x_1);
x_79 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_75, x_1, x_2);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = l_Lean_IR_ExplicitBoxing_getVarType(x_73, x_1, x_82);
x_86 = lean::cnstr_get(x_85, 0);
x_88 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_set(x_85, 0, lean::box(0));
 lean::cnstr_set(x_85, 1, lean::box(0));
 x_90 = x_85;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::dec(x_85);
 x_90 = lean::box(0);
}
x_91 = 5;
x_92 = lean::unbox(x_86);
x_93 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_92, x_91);
if (x_93 == 0)
{
obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_90);
x_95 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_88);
x_96 = lean::cnstr_get(x_95, 0);
x_98 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
x_101 = l_Lean_IR_ExplicitBoxing_mkCast(x_73, x_92);
lean::inc(x_96);
if (lean::is_scalar(x_77)) {
 x_103 = lean::alloc_cnstr(3, 4, 0);
} else {
 x_103 = x_77;
}
lean::cnstr_set(x_103, 0, x_69);
lean::cnstr_set(x_103, 1, x_71);
lean::cnstr_set(x_103, 2, x_96);
lean::cnstr_set(x_103, 3, x_80);
x_104 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_104, 0, x_96);
lean::cnstr_set(x_104, 1, x_101);
lean::cnstr_set(x_104, 2, x_103);
lean::cnstr_set_scalar(x_104, sizeof(void*)*3, x_91);
x_105 = x_104;
if (lean::is_scalar(x_100)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_100;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_98);
return x_106;
}
else
{
obj* x_107; obj* x_108; 
if (lean::is_scalar(x_77)) {
 x_107 = lean::alloc_cnstr(3, 4, 0);
} else {
 x_107 = x_77;
}
lean::cnstr_set(x_107, 0, x_69);
lean::cnstr_set(x_107, 1, x_71);
lean::cnstr_set(x_107, 2, x_73);
lean::cnstr_set(x_107, 3, x_80);
if (lean::is_scalar(x_90)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_90;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_88);
return x_108;
}
}
case 4:
{
obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_123; obj* x_125; obj* x_128; obj* x_129; obj* x_131; obj* x_133; uint8 x_134; uint8 x_135; 
x_109 = lean::cnstr_get(x_0, 0);
x_111 = lean::cnstr_get(x_0, 1);
x_113 = lean::cnstr_get(x_0, 2);
x_115 = lean::cnstr_get(x_0, 3);
x_117 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
x_118 = lean::cnstr_get(x_0, 4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 lean::cnstr_set(x_0, 4, lean::box(0));
 x_120 = x_0;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::inc(x_118);
 lean::dec(x_0);
 x_120 = lean::box(0);
}
lean::inc(x_1);
x_122 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_118, x_1, x_2);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
lean::dec(x_122);
x_128 = l_Lean_IR_ExplicitBoxing_getVarType(x_115, x_1, x_125);
x_129 = lean::cnstr_get(x_128, 0);
x_131 = lean::cnstr_get(x_128, 1);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_set(x_128, 0, lean::box(0));
 lean::cnstr_set(x_128, 1, lean::box(0));
 x_133 = x_128;
} else {
 lean::inc(x_129);
 lean::inc(x_131);
 lean::dec(x_128);
 x_133 = lean::box(0);
}
x_134 = lean::unbox(x_129);
x_135 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_134, x_117);
if (x_135 == 0)
{
obj* x_137; obj* x_138; obj* x_140; obj* x_142; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_133);
x_137 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_131);
x_138 = lean::cnstr_get(x_137, 0);
x_140 = lean::cnstr_get(x_137, 1);
if (lean::is_exclusive(x_137)) {
 x_142 = x_137;
} else {
 lean::inc(x_138);
 lean::inc(x_140);
 lean::dec(x_137);
 x_142 = lean::box(0);
}
x_143 = l_Lean_IR_ExplicitBoxing_mkCast(x_115, x_134);
lean::inc(x_138);
if (lean::is_scalar(x_120)) {
 x_145 = lean::alloc_cnstr(4, 5, 1);
} else {
 x_145 = x_120;
}
lean::cnstr_set(x_145, 0, x_109);
lean::cnstr_set(x_145, 1, x_111);
lean::cnstr_set(x_145, 2, x_113);
lean::cnstr_set(x_145, 3, x_138);
lean::cnstr_set(x_145, 4, x_123);
lean::cnstr_set_scalar(x_145, sizeof(void*)*5, x_117);
x_146 = x_145;
x_147 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_147, 0, x_138);
lean::cnstr_set(x_147, 1, x_143);
lean::cnstr_set(x_147, 2, x_146);
lean::cnstr_set_scalar(x_147, sizeof(void*)*3, x_117);
x_148 = x_147;
if (lean::is_scalar(x_142)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_142;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_140);
return x_149;
}
else
{
obj* x_150; obj* x_151; obj* x_152; 
if (lean::is_scalar(x_120)) {
 x_150 = lean::alloc_cnstr(4, 5, 1);
} else {
 x_150 = x_120;
}
lean::cnstr_set(x_150, 0, x_109);
lean::cnstr_set(x_150, 1, x_111);
lean::cnstr_set(x_150, 2, x_113);
lean::cnstr_set(x_150, 3, x_115);
lean::cnstr_set(x_150, 4, x_123);
lean::cnstr_set_scalar(x_150, sizeof(void*)*5, x_117);
x_151 = x_150;
if (lean::is_scalar(x_133)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_133;
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_131);
return x_152;
}
}
case 8:
{
obj* x_153; obj* x_155; obj* x_157; obj* x_158; obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_165; 
x_153 = lean::cnstr_get(x_0, 0);
x_155 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_157 = x_0;
} else {
 lean::inc(x_153);
 lean::inc(x_155);
 lean::dec(x_0);
 x_157 = lean::box(0);
}
x_158 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_155, x_1, x_2);
x_159 = lean::cnstr_get(x_158, 0);
x_161 = lean::cnstr_get(x_158, 1);
if (lean::is_exclusive(x_158)) {
 x_163 = x_158;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_158);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_164 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_164 = x_157;
}
lean::cnstr_set(x_164, 0, x_153);
lean::cnstr_set(x_164, 1, x_159);
if (lean::is_scalar(x_163)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_163;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_161);
return x_165;
}
case 9:
{
obj* x_166; obj* x_168; obj* x_170; obj* x_172; uint8 x_173; obj* x_174; obj* x_176; obj* x_177; obj* x_179; obj* x_182; obj* x_183; obj* x_185; obj* x_187; uint8 x_188; uint8 x_189; 
x_166 = lean::cnstr_get(x_0, 0);
x_168 = lean::cnstr_get(x_0, 1);
x_170 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_172 = x_0;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_0);
 x_172 = lean::box(0);
}
x_173 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_170);
x_174 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_176 = l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_174, x_170, x_1, x_2);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
lean::dec(x_176);
x_182 = l_Lean_IR_ExplicitBoxing_getVarType(x_168, x_1, x_179);
x_183 = lean::cnstr_get(x_182, 0);
x_185 = lean::cnstr_get(x_182, 1);
if (lean::is_exclusive(x_182)) {
 lean::cnstr_set(x_182, 0, lean::box(0));
 lean::cnstr_set(x_182, 1, lean::box(0));
 x_187 = x_182;
} else {
 lean::inc(x_183);
 lean::inc(x_185);
 lean::dec(x_182);
 x_187 = lean::box(0);
}
x_188 = lean::unbox(x_183);
x_189 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_188, x_173);
if (x_189 == 0)
{
obj* x_191; obj* x_192; obj* x_194; obj* x_196; obj* x_197; obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
lean::dec(x_187);
x_191 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_185);
x_192 = lean::cnstr_get(x_191, 0);
x_194 = lean::cnstr_get(x_191, 1);
if (lean::is_exclusive(x_191)) {
 x_196 = x_191;
} else {
 lean::inc(x_192);
 lean::inc(x_194);
 lean::dec(x_191);
 x_196 = lean::box(0);
}
x_197 = l_Lean_IR_ExplicitBoxing_mkCast(x_168, x_188);
lean::inc(x_192);
if (lean::is_scalar(x_172)) {
 x_199 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_199 = x_172;
}
lean::cnstr_set(x_199, 0, x_166);
lean::cnstr_set(x_199, 1, x_192);
lean::cnstr_set(x_199, 2, x_177);
x_200 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_200, 0, x_192);
lean::cnstr_set(x_200, 1, x_197);
lean::cnstr_set(x_200, 2, x_199);
lean::cnstr_set_scalar(x_200, sizeof(void*)*3, x_173);
x_201 = x_200;
if (lean::is_scalar(x_196)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_196;
}
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_194);
return x_202;
}
else
{
obj* x_203; obj* x_204; 
if (lean::is_scalar(x_172)) {
 x_203 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_203 = x_172;
}
lean::cnstr_set(x_203, 0, x_166);
lean::cnstr_set(x_203, 1, x_168);
lean::cnstr_set(x_203, 2, x_177);
if (lean::is_scalar(x_187)) {
 x_204 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_204 = x_187;
}
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_185);
return x_204;
}
}
case 10:
{
obj* x_205; obj* x_207; obj* x_208; 
x_205 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_207 = x_0;
} else {
 lean::inc(x_205);
 lean::dec(x_0);
 x_207 = lean::box(0);
}
x_208 = l_Lean_IR_ExplicitBoxing_getResultType(x_1, x_2);
if (lean::obj_tag(x_205) == 0)
{
obj* x_209; obj* x_211; obj* x_214; obj* x_216; obj* x_217; obj* x_218; obj* x_220; obj* x_222; uint8 x_223; uint8 x_224; uint8 x_225; 
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
x_214 = lean::cnstr_get(x_205, 0);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_set(x_205, 0, lean::box(0));
 x_216 = x_205;
} else {
 lean::inc(x_214);
 lean::dec(x_205);
 x_216 = lean::box(0);
}
x_217 = l_Lean_IR_ExplicitBoxing_getVarType(x_214, x_1, x_211);
x_218 = lean::cnstr_get(x_217, 0);
x_220 = lean::cnstr_get(x_217, 1);
if (lean::is_exclusive(x_217)) {
 lean::cnstr_set(x_217, 0, lean::box(0));
 lean::cnstr_set(x_217, 1, lean::box(0));
 x_222 = x_217;
} else {
 lean::inc(x_218);
 lean::inc(x_220);
 lean::dec(x_217);
 x_222 = lean::box(0);
}
x_223 = lean::unbox(x_218);
x_224 = lean::unbox(x_209);
x_225 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_223, x_224);
if (x_225 == 0)
{
obj* x_227; obj* x_228; obj* x_230; obj* x_232; obj* x_233; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_222);
x_227 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_220);
x_228 = lean::cnstr_get(x_227, 0);
x_230 = lean::cnstr_get(x_227, 1);
if (lean::is_exclusive(x_227)) {
 x_232 = x_227;
} else {
 lean::inc(x_228);
 lean::inc(x_230);
 lean::dec(x_227);
 x_232 = lean::box(0);
}
x_233 = l_Lean_IR_ExplicitBoxing_mkCast(x_214, x_223);
lean::inc(x_228);
if (lean::is_scalar(x_216)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_216;
}
lean::cnstr_set(x_235, 0, x_228);
if (lean::is_scalar(x_207)) {
 x_236 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_236 = x_207;
}
lean::cnstr_set(x_236, 0, x_235);
x_237 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_237, 0, x_228);
lean::cnstr_set(x_237, 1, x_233);
lean::cnstr_set(x_237, 2, x_236);
lean::cnstr_set_scalar(x_237, sizeof(void*)*3, x_224);
x_238 = x_237;
if (lean::is_scalar(x_232)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_232;
}
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_230);
return x_239;
}
else
{
obj* x_240; obj* x_241; obj* x_242; 
if (lean::is_scalar(x_216)) {
 x_240 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_240 = x_216;
}
lean::cnstr_set(x_240, 0, x_214);
if (lean::is_scalar(x_207)) {
 x_241 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_241 = x_207;
}
lean::cnstr_set(x_241, 0, x_240);
if (lean::is_scalar(x_222)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_222;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_220);
return x_242;
}
}
else
{
obj* x_244; obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_1);
x_244 = lean::cnstr_get(x_208, 1);
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 x_246 = x_208;
} else {
 lean::inc(x_244);
 lean::dec(x_208);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_207)) {
 x_247 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_247 = x_207;
}
lean::cnstr_set(x_247, 0, x_205);
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_244);
return x_248;
}
}
case 11:
{
obj* x_249; obj* x_251; obj* x_253; obj* x_255; obj* x_256; obj* x_258; obj* x_261; obj* x_264; obj* x_266; obj* x_269; obj* x_271; obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
x_249 = lean::cnstr_get(x_0, 0);
x_251 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_253 = x_0;
} else {
 lean::inc(x_249);
 lean::inc(x_251);
 lean::dec(x_0);
 x_253 = lean::box(0);
}
lean::inc(x_1);
x_255 = l_Lean_IR_ExplicitBoxing_getJPParams(x_249, x_1, x_2);
x_256 = lean::cnstr_get(x_255, 0);
lean::inc(x_256);
x_258 = lean::cnstr_get(x_255, 1);
lean::inc(x_258);
lean::dec(x_255);
x_261 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_256, x_251, x_1, x_258);
lean::dec(x_251);
lean::dec(x_256);
x_264 = lean::cnstr_get(x_261, 0);
lean::inc(x_264);
x_266 = lean::cnstr_get(x_261, 1);
lean::inc(x_266);
lean::dec(x_261);
x_269 = lean::cnstr_get(x_264, 0);
x_271 = lean::cnstr_get(x_264, 1);
if (lean::is_exclusive(x_264)) {
 x_273 = x_264;
} else {
 lean::inc(x_269);
 lean::inc(x_271);
 lean::dec(x_264);
 x_273 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_274 = lean::alloc_cnstr(11, 2, 0);
} else {
 x_274 = x_253;
}
lean::cnstr_set(x_274, 0, x_249);
lean::cnstr_set(x_274, 1, x_269);
x_275 = l_Lean_IR_reshape(x_271, x_274);
if (lean::is_scalar(x_273)) {
 x_276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_276 = x_273;
}
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_266);
return x_276;
}
default:
{
obj* x_278; 
lean::dec(x_1);
x_278 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_278, 0, x_0);
lean::cnstr_set(x_278, 1, x_2);
return x_278;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* initialize_init_control_estate(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_boxing(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_estate(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1();
lean::mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1);
 l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1___closed__1);
return w;
}
