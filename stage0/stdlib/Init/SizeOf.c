// Lean compiler output
// Module: Init.SizeOf
// Imports: Init.Core
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_instSizeOf(lean_object*);
lean_object* l_instSizeOfSum___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfProd(lean_object*, lean_object*);
lean_object* l_instSizeOfSubtype(lean_object*);
lean_object* l_instSizeOfNat(lean_object*);
lean_object* l_instSizeOfPUnit___boxed(lean_object*);
lean_object* l_instSizeOfPSum_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfPUnit(lean_object*);
lean_object* l_instSizeOfSubtype___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instSizeOfProd_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfProd_match__1___rarg(lean_object*, lean_object*);
lean_object* l_instSizeOfPSum___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfList_loop(lean_object*);
lean_object* l_instSizeOfList___rarg(lean_object*);
lean_object* l_instSizeOfPSum(lean_object*, lean_object*);
lean_object* l_instSizeOfPSigma(lean_object*, lean_object*);
lean_object* l_instSizeOfBool___boxed(lean_object*);
lean_object* l_instSizeOfOption(lean_object*);
lean_object* l_instSizeOfSigma(lean_object*, lean_object*);
lean_object* l_instSizeOfSubtype_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfList(lean_object*);
lean_object* l_instSizeOf___closed__1;
lean_object* l_instSizeOfPSigma_match__1___rarg(lean_object*, lean_object*);
lean_object* l_instSizeOfOption_match__1(lean_object*, lean_object*);
lean_object* l_instSizeOfSigma___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfSum_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfSum(lean_object*, lean_object*);
lean_object* l_instSizeOfList_loop___rarg(lean_object*, lean_object*);
lean_object* l_instSizeOfPSigma_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfPSum_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfList_loop_match__1(lean_object*, lean_object*);
lean_object* l_default_sizeOf___boxed(lean_object*, lean_object*);
lean_object* l_instSizeOfSum_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfList_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfSigma_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfNat___boxed(lean_object*);
lean_object* l_instSizeOfSigma_match__1___rarg(lean_object*, lean_object*);
lean_object* l_default_sizeOf_match__1(lean_object*, lean_object*);
lean_object* l_default_sizeOf(lean_object*, lean_object*);
lean_object* l_instSizeOfProd___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfOption___rarg(lean_object*, lean_object*);
lean_object* l_instSizeOfPSigma___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_default_sizeOf_match__1___rarg(lean_object*, lean_object*);
lean_object* l_instSizeOfSubtype_match__1___rarg(lean_object*, lean_object*);
lean_object* l_instSizeOfOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSizeOfBool(uint8_t);
lean_object* l_default_sizeOf_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_default_sizeOf_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_default_sizeOf_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_default_sizeOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
lean_object* l_default_sizeOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_default_sizeOf(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_instSizeOf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_default_sizeOf___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l_instSizeOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOf___closed__1;
return x_2;
}
}
lean_object* l_instSizeOfNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_instSizeOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOfNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instSizeOfProd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instSizeOfProd_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instSizeOfProd_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_instSizeOfProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_7, x_6);
lean_dec(x_6);
x_9 = lean_apply_1(x_2, x_5);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_instSizeOfProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfProd___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfSum_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_instSizeOfSum_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instSizeOfSum_match__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_instSizeOfSum___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_10, x_9);
lean_dec(x_9);
return x_11;
}
}
}
lean_object* l_instSizeOfSum(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfSum___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfPSum_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_instSizeOfPSum_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instSizeOfPSum_match__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_instSizeOfPSum___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_10, x_9);
lean_dec(x_9);
return x_11;
}
}
}
lean_object* l_instSizeOfPSum(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfPSum___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfSigma_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instSizeOfSigma_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instSizeOfSigma_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_instSizeOfSigma___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_7, x_6);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_4, x_5);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_instSizeOfSigma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfSigma___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfPSigma_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instSizeOfPSigma_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instSizeOfPSigma_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_instSizeOfPSigma___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_7, x_6);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_4, x_5);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_instSizeOfPSigma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfPSigma___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfPUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
}
lean_object* l_instSizeOfPUnit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOfPUnit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instSizeOfBool(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
}
lean_object* l_instSizeOfBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instSizeOfBool(x_2);
return x_3;
}
}
lean_object* l_instSizeOfOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_instSizeOfOption_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfOption_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
}
lean_object* l_instSizeOfOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSizeOfOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_instSizeOfList_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_instSizeOfList_loop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instSizeOfList_loop_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instSizeOfList_loop___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_7, x_6);
lean_dec(x_6);
x_9 = l_instSizeOfList_loop___rarg(x_1, x_5);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
}
lean_object* l_instSizeOfList_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSizeOfList_loop___rarg), 2, 0);
return x_2;
}
}
lean_object* l_instSizeOfList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSizeOfList_loop___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_instSizeOfList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSizeOfList___rarg), 1, 0);
return x_2;
}
}
lean_object* l_instSizeOfSubtype_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
lean_object* l_instSizeOfSubtype_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instSizeOfSubtype_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_instSizeOfSubtype___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_instSizeOfSubtype(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSizeOfSubtype___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init_Core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_SizeOf(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instSizeOf___closed__1 = _init_l_instSizeOf___closed__1();
lean_mark_persistent(l_instSizeOf___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
