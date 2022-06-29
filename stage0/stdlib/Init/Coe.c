// Lean compiler output
// Module: Init.Coe
// Imports: Init.Prelude
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
LEAN_EXPORT lean_object* l_coeBase___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeDep___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfHead___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeTail__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfDep___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_coeSortToCoeTail(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeTail___rarg(lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__9;
LEAN_EXPORT lean_object* l_coeSortToCoeTail___rarg(lean_object*);
LEAN_EXPORT lean_object* l_coeOfTCOfTail(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfHTCT___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfTC___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decPropToBool___rarg(uint8_t);
LEAN_EXPORT lean_object* l_coeBase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_liftCoeM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeTrans(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfTail(lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__5;
LEAN_EXPORT lean_object* l_coeOfHeadOfTC___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__8;
LEAN_EXPORT lean_object* l_Lean_Internal_liftCoeM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decPropToBool___rarg___boxed(lean_object*);
static lean_object* l_coeNotation___closed__4;
LEAN_EXPORT lean_object* l_instCoeDep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeNotation;
LEAN_EXPORT lean_object* l_coeSortToCoeTail___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_liftCoeM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__3;
LEAN_EXPORT lean_object* l_Lean_Internal_coeM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfHTCT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_boolToSort;
LEAN_EXPORT lean_object* l_coeOfHeadOfTC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfTCOfTail___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_coeM(lean_object*, lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__2;
LEAN_EXPORT lean_object* l_subtypeCoe___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_coeOfHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_optionCoe___rarg(lean_object*);
LEAN_EXPORT lean_object* l_coeOfDep___rarg(lean_object*);
LEAN_EXPORT lean_object* l_coeOfTC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfTail___rarg(lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__7;
LEAN_EXPORT lean_object* l_instCoeTail__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coeOfDep___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__11;
LEAN_EXPORT lean_object* l_coeTrans___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_optionCoe(lean_object*);
LEAN_EXPORT lean_object* l_coeId(lean_object*);
LEAN_EXPORT lean_object* l_subtypeCoe___rarg(lean_object*);
LEAN_EXPORT lean_object* l_subtypeCoe(lean_object*, lean_object*);
static lean_object* l_coeNotation___closed__6;
LEAN_EXPORT lean_object* l_coeOfHeafOfTCOfTail___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_boolToProp;
LEAN_EXPORT lean_object* l_coeId___rarg(lean_object*);
LEAN_EXPORT lean_object* l_coeId___rarg___boxed(lean_object*);
static lean_object* l_coeNotation___closed__1;
static lean_object* l_coeNotation___closed__10;
LEAN_EXPORT lean_object* l_instCoeTail(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decPropToBool(lean_object*);
LEAN_EXPORT lean_object* l_coeOfHeafOfTCOfTail(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_coeNotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coeNotation", 11);
return x_1;
}
}
static lean_object* _init_l_coeNotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_coeNotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_coeNotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_coeNotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_coeNotation___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_coeNotation___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("↑", 3);
return x_1;
}
}
static lean_object* _init_l_coeNotation___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_coeNotation___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_coeNotation___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_coeNotation___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_coeNotation___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_coeNotation___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_coeNotation___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_coeNotation___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_coeNotation___closed__4;
x_2 = l_coeNotation___closed__6;
x_3 = l_coeNotation___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_coeNotation___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_coeNotation___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_coeNotation___closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_coeNotation() {
_start:
{
lean_object* x_1; 
x_1 = l_coeNotation___closed__11;
return x_1;
}
}
LEAN_EXPORT lean_object* l_coeTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_coeTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeTrans___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_coeBase___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeBase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeBase___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfHeafOfTCOfTail___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_coeOfHeafOfTCOfTail(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_coeOfHeafOfTCOfTail___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_coeOfHeadOfTC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_coeOfHeadOfTC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeOfHeadOfTC___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_coeOfTCOfTail___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_coeOfTCOfTail(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeOfTCOfTail___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_coeOfHead___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfHead(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfHead___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfTail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfTail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfTail___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfTC___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfTC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfTC___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfHTCT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfHTCT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeOfHTCT___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeOfDep___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_coeOfDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeOfDep___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_coeOfDep___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coeOfDep___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_coeOfDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_coeOfDep(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_coeId___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_coeId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeId___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_coeId___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coeId___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_coeSortToCoeTail___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_coeSortToCoeTail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeSortToCoeTail___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_coeSortToCoeTail___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coeSortToCoeTail___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_boolToProp() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_boolToSort() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT uint8_t l_decPropToBool___rarg(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_decPropToBool(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_decPropToBool___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_decPropToBool___rarg___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_optionCoe___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_optionCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_optionCoe___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_subtypeCoe___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_subtypeCoe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_subtypeCoe___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_subtypeCoe___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_subtypeCoe___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_liftCoeM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_liftCoeM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, lean_box(0), x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Internal_liftCoeM___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_liftCoeM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Internal_liftCoeM___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_coeM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Internal_liftCoeM___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_coeM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Internal_coeM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instCoeDep___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instCoeDep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instCoeDep___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instCoeTail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instCoeTail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instCoeTail___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instCoeTail__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instCoeTail__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instCoeTail__1___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Coe(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_coeNotation___closed__1 = _init_l_coeNotation___closed__1();
lean_mark_persistent(l_coeNotation___closed__1);
l_coeNotation___closed__2 = _init_l_coeNotation___closed__2();
lean_mark_persistent(l_coeNotation___closed__2);
l_coeNotation___closed__3 = _init_l_coeNotation___closed__3();
lean_mark_persistent(l_coeNotation___closed__3);
l_coeNotation___closed__4 = _init_l_coeNotation___closed__4();
lean_mark_persistent(l_coeNotation___closed__4);
l_coeNotation___closed__5 = _init_l_coeNotation___closed__5();
lean_mark_persistent(l_coeNotation___closed__5);
l_coeNotation___closed__6 = _init_l_coeNotation___closed__6();
lean_mark_persistent(l_coeNotation___closed__6);
l_coeNotation___closed__7 = _init_l_coeNotation___closed__7();
lean_mark_persistent(l_coeNotation___closed__7);
l_coeNotation___closed__8 = _init_l_coeNotation___closed__8();
lean_mark_persistent(l_coeNotation___closed__8);
l_coeNotation___closed__9 = _init_l_coeNotation___closed__9();
lean_mark_persistent(l_coeNotation___closed__9);
l_coeNotation___closed__10 = _init_l_coeNotation___closed__10();
lean_mark_persistent(l_coeNotation___closed__10);
l_coeNotation___closed__11 = _init_l_coeNotation___closed__11();
lean_mark_persistent(l_coeNotation___closed__11);
l_coeNotation = _init_l_coeNotation();
lean_mark_persistent(l_coeNotation);
l_boolToProp = _init_l_boolToProp();
l_boolToSort = _init_l_boolToSort();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
