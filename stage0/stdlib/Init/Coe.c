// Lean compiler output
// Module: Init.Coe
// Imports: Init.HasCoe Init.Core
#include "runtime/lean.h"
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
lean_object* l_coeTC(lean_object*, lean_object*);
lean_object* l_coeBase___rarg(lean_object*, lean_object*);
lean_object* l_coeOfHead___rarg(lean_object*, lean_object*);
lean_object* l_coeTail___rarg(lean_object*, lean_object*);
lean_object* l_coeOfDep___rarg___boxed(lean_object*);
lean_object* l_coeOfDep(lean_object*, lean_object*, lean_object*);
lean_object* l_coeD___rarg(lean_object*);
lean_object* l_coeOfTCOfTail(lean_object*, lean_object*, lean_object*);
lean_object* l_coeTC___rarg(lean_object*, lean_object*);
lean_object* l_coeTail(lean_object*, lean_object*);
lean_object* l_coeOfTC___rarg(lean_object*, lean_object*);
lean_object* l_coeFun(lean_object*, lean_object*);
uint8_t l_decPropToBool___rarg(uint8_t);
lean_object* l_coeBase(lean_object*, lean_object*);
lean_object* l_coeTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_coeB___rarg(lean_object*, lean_object*);
lean_object* l_coeOfTail(lean_object*, lean_object*);
lean_object* l_coeSortTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_coeOfHeadOfTC___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_decPropToBool___rarg___boxed(lean_object*);
lean_object* l_coeSort___rarg(lean_object*, lean_object*);
lean_object* l_hasOfNatOfCoe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeFunTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeOfHeadOfTC(lean_object*, lean_object*, lean_object*);
lean_object* l_coeOfTCOfTail___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_subtypeCoe___rarg___boxed(lean_object*);
lean_object* l_coeOfHead(lean_object*, lean_object*);
lean_object* l_optionCoe___rarg(lean_object*);
lean_object* l_hasOfNatOfCoe(lean_object*, lean_object*);
lean_object* l_coeFunTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_coeOfDep___rarg(lean_object*);
lean_object* l_coeOfTC(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_coeD___rarg___boxed(lean_object*);
lean_object* l_coeOfTail___rarg(lean_object*, lean_object*);
lean_object* l_coe___rarg(lean_object*);
lean_object* l_coe(lean_object*, lean_object*, lean_object*);
lean_object* l_coeSortTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeDecidableEq___boxed(lean_object*);
lean_object* l_coeOfDep___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_coeTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_optionCoe(lean_object*);
lean_object* l_subtypeCoe___rarg(lean_object*);
lean_object* l_coeFun___rarg(lean_object*, lean_object*);
lean_object* l_coeB(lean_object*, lean_object*);
lean_object* l_subtypeCoe(lean_object*, lean_object*);
lean_object* l_coeSort(lean_object*, lean_object*);
lean_object* l_coeOfHeafOfTCOfTail___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_coe___rarg___boxed(lean_object*);
lean_object* l_boolToProp;
lean_object* l_coeHead___rarg(lean_object*, lean_object*);
lean_object* l_coeD___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_decPropToBool(lean_object*);
lean_object* l_coeOfHeafOfTCOfTail(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_coeHead(lean_object*, lean_object*);
lean_object* l_coeD(lean_object*, lean_object*, lean_object*);
lean_object* l_coeB___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeB(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeB___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeHead___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeHead(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeHead___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeTail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeTail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeTail___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeD___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_coeD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeD___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_coeD___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coeD___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_coeD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_coeD(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_coeTC___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeTC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeTC___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coe___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_coe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coe___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_coe___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coe___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_coe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_coe(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_coeFun___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_coeFun(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeFun___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeSort___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_coeSort(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeSort___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_coeTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* l_coeBase___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeBase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeBase___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeOfHeafOfTCOfTail___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_4, x_1);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
lean_object* l_coeOfHeafOfTCOfTail(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_coeOfHeafOfTCOfTail___rarg), 4, 0);
return x_5;
}
}
lean_object* l_coeOfHeadOfTC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_3, x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_coeOfHeadOfTC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeOfHeadOfTC___rarg), 3, 0);
return x_4;
}
}
lean_object* l_coeOfTCOfTail___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* l_coeOfTCOfTail(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeOfTCOfTail___rarg), 3, 0);
return x_4;
}
}
lean_object* l_coeOfHead___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_coeOfHead(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfHead___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeOfTail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_coeOfTail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfTail___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeOfTC___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_coeOfTC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfTC___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeOfDep___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_coeOfDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeOfDep___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_coeOfDep___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coeOfDep___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_coeOfDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_coeOfDep(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_coeFunTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_coeFunTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeFunTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* l_coeSortTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_coeSortTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeSortTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* _init_l_boolToProp() {
_start:
{
return lean_box(0);
}
}
uint8_t l_coeDecidableEq(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_coeDecidableEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_coeDecidableEq(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_decPropToBool___rarg(uint8_t x_1) {
_start:
{
return x_1;
}
}
lean_object* l_decPropToBool(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_decPropToBool___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_decPropToBool___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_decPropToBool___rarg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_optionCoe___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_optionCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_optionCoe___rarg), 1, 0);
return x_2;
}
}
lean_object* l_subtypeCoe___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_subtypeCoe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_subtypeCoe___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_subtypeCoe___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_subtypeCoe___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_hasOfNatOfCoe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_hasOfNatOfCoe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_hasOfNatOfCoe___rarg), 3, 0);
return x_3;
}
}
lean_object* initialize_Init_HasCoe(lean_object*);
lean_object* initialize_Init_Core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Coe(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_HasCoe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_boolToProp = _init_l_boolToProp();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
