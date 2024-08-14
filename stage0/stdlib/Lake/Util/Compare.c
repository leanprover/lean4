// Lean compiler output
// Module: Lake.Util.Compare
// Imports: Init
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
static lean_object* l_Lake_instLawfulCmpEqNatCompare___closed__1;
static lean_object* l_Lake_instLawfulCmpEqStringCompare___closed__1;
LEAN_EXPORT lean_object* l_Lake_instEqOfCmpWrtOfEqOfCmp(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqNatCompare;
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lake_instLawfulCmpEqUInt64Compare___lambda__1(uint64_t, uint64_t);
static lean_object* l_Lake_instLawfulCmpEqNatCompare___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_instLawfulCmpEqUInt64Compare___closed__1;
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqStringCompare___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqUInt64Compare;
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqNatCompare___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instLawfulCmpEqNatCompare___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lake_instLawfulCmpEqUInt64Compare___closed__2;
static lean_object* l_Lake_instLawfulCmpEqStringCompare___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEqOfCmpWrtOfEqOfCmp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqUInt64Compare___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instLawfulCmpEqStringCompare___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqStringCompare;
LEAN_EXPORT lean_object* l_Lake_instEqOfCmpWrtOfEqOfCmp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEqOfCmpWrtOfEqOfCmp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instEqOfCmpWrtOfEqOfCmp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instEqOfCmpWrtOfEqOfCmp___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instEqOfCmpWrtOfEqOfCmp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_instEqOfCmpWrtOfEqOfCmp___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lake_instLawfulCmpEqNatCompare___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqNatCompare___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instLawfulCmpEqNatCompare___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqNatCompare___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqNatCompare() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instLawfulCmpEqNatCompare___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqNatCompare___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instLawfulCmpEqNatCompare___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instLawfulCmpEqUInt64Compare___lambda__1(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint64_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqUInt64Compare___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instLawfulCmpEqUInt64Compare___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqUInt64Compare___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqUInt64Compare() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instLawfulCmpEqUInt64Compare___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqUInt64Compare___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_instLawfulCmpEqUInt64Compare___lambda__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instLawfulCmpEqStringCompare___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqStringCompare___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instLawfulCmpEqStringCompare___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqStringCompare___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLawfulCmpEqStringCompare() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instLawfulCmpEqStringCompare___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instLawfulCmpEqStringCompare___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instLawfulCmpEqStringCompare___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Compare(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instLawfulCmpEqNatCompare___closed__1 = _init_l_Lake_instLawfulCmpEqNatCompare___closed__1();
lean_mark_persistent(l_Lake_instLawfulCmpEqNatCompare___closed__1);
l_Lake_instLawfulCmpEqNatCompare___closed__2 = _init_l_Lake_instLawfulCmpEqNatCompare___closed__2();
lean_mark_persistent(l_Lake_instLawfulCmpEqNatCompare___closed__2);
l_Lake_instLawfulCmpEqNatCompare = _init_l_Lake_instLawfulCmpEqNatCompare();
lean_mark_persistent(l_Lake_instLawfulCmpEqNatCompare);
l_Lake_instLawfulCmpEqUInt64Compare___closed__1 = _init_l_Lake_instLawfulCmpEqUInt64Compare___closed__1();
lean_mark_persistent(l_Lake_instLawfulCmpEqUInt64Compare___closed__1);
l_Lake_instLawfulCmpEqUInt64Compare___closed__2 = _init_l_Lake_instLawfulCmpEqUInt64Compare___closed__2();
lean_mark_persistent(l_Lake_instLawfulCmpEqUInt64Compare___closed__2);
l_Lake_instLawfulCmpEqUInt64Compare = _init_l_Lake_instLawfulCmpEqUInt64Compare();
lean_mark_persistent(l_Lake_instLawfulCmpEqUInt64Compare);
l_Lake_instLawfulCmpEqStringCompare___closed__1 = _init_l_Lake_instLawfulCmpEqStringCompare___closed__1();
lean_mark_persistent(l_Lake_instLawfulCmpEqStringCompare___closed__1);
l_Lake_instLawfulCmpEqStringCompare___closed__2 = _init_l_Lake_instLawfulCmpEqStringCompare___closed__2();
lean_mark_persistent(l_Lake_instLawfulCmpEqStringCompare___closed__2);
l_Lake_instLawfulCmpEqStringCompare = _init_l_Lake_instLawfulCmpEqStringCompare();
lean_mark_persistent(l_Lake_instLawfulCmpEqStringCompare);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
