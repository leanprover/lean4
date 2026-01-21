// Lean compiler output
// Module: Init.Data.ToString.Basic
// Imports: public import Init.Data.Repr public import Init.Data.Option.Basic
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
static lean_object* l_addParenHeuristic___closed__4;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt___lam__0(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_instReprExcept___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object*, lean_object*);
static lean_object* l_instToStringExcept___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instToStringUInt16;
static lean_object* l_List_toString___redArg___closed__2;
LEAN_EXPORT lean_object* l_instToStringRaw__1;
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object*, lean_object*);
static lean_object* l_instToStringSum___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object*, lean_object*);
static lean_object* l_instToStringNat___closed__0;
LEAN_EXPORT lean_object* l_instToStringChar;
LEAN_EXPORT lean_object* l_instToStringList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringList___redArg(lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static lean_object* l_instToStringOption___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instToStringUInt32;
LEAN_EXPORT lean_object* l_instToStringFin(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFormat;
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object*, lean_object*);
static lean_object* l_instToStringRaw___closed__0;
static lean_object* l_instToStringChar___closed__0;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instToStringRaw;
static lean_object* l_instToStringUInt8___closed__0;
static lean_object* l_instToStringInt___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instToStringPUnit;
static lean_object* l_instToStringBool___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_instToStringSigma___redArg___lam__0___closed__0;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_List_toString___redArg___closed__0;
LEAN_EXPORT lean_object* l_instToStringId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object*);
static lean_object* l_instReprExcept___redArg___lam__0___closed__3;
static lean_object* l_List_toString___redArg___closed__1;
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t);
static lean_object* l_instToStringBool___lam__0___closed__0;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_instToStringULift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_addParenHeuristic___closed__2;
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instToStringUInt32___closed__0;
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instToStringDecidable___closed__0;
LEAN_EXPORT lean_object* l_instToStringNat;
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringUInt8;
static lean_object* l_instReprExcept___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_addParenHeuristic___closed__0;
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_instToStringInt___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instToStringBool;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t);
static lean_object* l_instToStringUInt64___closed__0;
static lean_object* l_instToStringFormat___closed__0;
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_instToStringPUnit___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt;
static lean_object* l_instToStringInt___closed__0;
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt64;
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_instToStringString___closed__0;
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t);
static lean_object* l_instToStringChar___lam__0___closed__0;
static lean_object* l_instToStringUSize___closed__0;
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprExcept___redArg___lam__0___closed__1;
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_instToStringOption___redArg___lam__0___closed__1;
static lean_object* l_addParenHeuristic___closed__3;
lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object*);
static lean_object* l_instToStringBool___closed__0;
LEAN_EXPORT lean_object* l_instToStringUnit;
static lean_object* l_addParenHeuristic___closed__1;
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instToStringSum___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object*);
static lean_object* l_instToStringExcept___redArg___lam__0___closed__0;
static lean_object* l_List_toString___redArg___lam__0___closed__0;
static lean_object* l_instToStringSigma___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instReprExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUSize;
LEAN_EXPORT lean_object* l_instToStringInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringString;
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_instToStringUInt16___closed__0;
static lean_object* l_instToStringPUnit___closed__0;
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringId___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToStringId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringId__1___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToStringId__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringString___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringString___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringString() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringString___closed__0;
return x_1;
}
}
static lean_object* _init_l_instToStringRaw___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Substring_Raw_Internal_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringRaw() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringRaw___closed__0;
return x_1;
}
}
static lean_object* _init_l_instToStringChar___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instToStringChar___lam__0___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instToStringChar___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringChar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringChar___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringChar() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringChar___closed__0;
return x_1;
}
}
static lean_object* _init_l_instToStringBool___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_instToStringBool___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_instToStringBool___lam__0___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_instToStringBool___lam__0___closed__1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToStringBool___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringBool___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringBool___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringBool() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringBool___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_instToStringBool___lam__0___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_instToStringBool___lam__0___closed__1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToStringDecidable___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringDecidable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringDecidable___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringDecidable___closed__0;
return x_2;
}
}
static lean_object* _init_l_List_toString___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_List_toString___redArg___lam__0___closed__0;
x_5 = lean_string_append(x_2, x_4);
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
return x_7;
}
}
static lean_object* _init_l_List_toString___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_List_toString___redArg___closed__0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_List_toString___redArg___closed__1;
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = l_List_toString___redArg___closed__2;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; 
lean_inc(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_List_toString___redArg___lam__0), 3, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_List_toString___redArg___closed__1;
x_14 = lean_apply_1(x_1, x_11);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l_List_foldl___redArg(x_12, x_15, x_4);
x_17 = 93;
x_18 = lean_string_push(x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_toString___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToStringList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toString), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_toString), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringPUnit___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("()", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringPUnit___lam__0___closed__0;
return x_2;
}
}
static lean_object* _init_l_instToStringPUnit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringPUnit___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringPUnit() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringPUnit___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringULift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUnit() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringPUnit___closed__0;
return x_1;
}
}
static lean_object* _init_l_instToStringNat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reprFast), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringNat() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringNat___closed__0;
return x_1;
}
}
static lean_object* _init_l_instToStringRaw__1() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringNat___closed__0;
return x_1;
}
}
static lean_object* _init_l_instToStringInt___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringInt___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_instToStringInt___lam__0___closed__0;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = l_Nat_reprFast(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = l_instToStringInt___lam__0___closed__1;
x_10 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_11 = l_Nat_reprFast(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringInt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringInt___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringInt() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringInt___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringNat___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringFin(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_Nat_reprFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToStringUInt8___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt8___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt8___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringUInt8___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Nat_reprFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToStringUInt16___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt16___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt16___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringUInt16___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Nat_reprFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt32___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt32___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt32___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringUInt32___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Nat_reprFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt64___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt64___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt64___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringUInt64___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Nat_reprFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_instToStringUSize___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUSize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUSize___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringUSize___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Std_Format_defWidth;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Std_Format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_instToStringFormat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringFormat___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringFormat___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_8; uint8_t x_9; 
x_8 = 32;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 9;
x_11 = lean_uint32_dec_eq(x_1, x_10);
x_2 = x_11;
goto block_7;
}
else
{
x_2 = x_9;
goto block_7;
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 13;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 10;
x_6 = lean_uint32_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_addParenHeuristic___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_addParenHeuristic___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_addParenHeuristic___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_addParenHeuristic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_addParenHeuristic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
static lean_object* _init_l_addParenHeuristic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_addParenHeuristic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_14; 
x_2 = l_addParenHeuristic___closed__0;
x_3 = l_addParenHeuristic___closed__1;
lean_inc_ref(x_1);
x_14 = lean_string_isprefixof(x_3, x_1);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_List_toString___redArg___closed__1;
lean_inc_ref(x_1);
x_16 = lean_string_isprefixof(x_15, x_1);
x_4 = x_16;
goto block_13;
}
else
{
x_4 = x_14;
goto block_13;
}
block_13:
{
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_addParenHeuristic___closed__2;
lean_inc_ref(x_1);
x_6 = lean_string_isprefixof(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_addParenHeuristic___closed__3;
lean_inc_ref(x_1);
x_8 = lean_string_isprefixof(x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc_ref(x_1);
x_9 = lean_string_any(x_1, x_2);
if (x_9 == 0)
{
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_string_append(x_3, x_1);
lean_dec_ref(x_1);
x_11 = l_addParenHeuristic___closed__4;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
}
static lean_object* _init_l_instToStringOption___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_instToStringOption___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(some ", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_instToStringOption___redArg___lam__0___closed__0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_instToStringOption___redArg___lam__0___closed__1;
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_addParenHeuristic(x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = l_addParenHeuristic___closed__4;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringSum___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(inl ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_instToStringSum___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(inr ", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_instToStringSum___redArg___lam__0___closed__0;
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_addParenHeuristic(x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = l_addParenHeuristic___closed__4;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_instToStringSum___redArg___lam__0___closed__1;
x_13 = lean_apply_1(x_2, x_11);
x_14 = l_addParenHeuristic(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = l_addParenHeuristic___closed__4;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_addParenHeuristic___closed__1;
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = l_List_toString___redArg___lam__0___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_1(x_2, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = l_addParenHeuristic___closed__4;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_instToStringSigma___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨", 3, 1);
return x_1;
}
}
static lean_object* _init_l_instToStringSigma___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟩", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_instToStringSigma___redArg___lam__0___closed__0;
lean_inc(x_4);
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = l_List_toString___redArg___lam__0___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_2(x_2, x_4, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = l_instToStringSigma___redArg___lam__0___closed__1;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_instToStringExcept___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_instToStringExcept___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ok: ", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_instToStringExcept___redArg___lam__0___closed__0;
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = l_instToStringExcept___redArg___lam__0___closed__1;
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_instReprExcept___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Except.error ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_instReprExcept___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprExcept___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprExcept___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Except.ok ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_instReprExcept___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprExcept___redArg___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_instReprExcept___redArg___lam__0___closed__1;
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_instReprExcept___redArg___lam__0___closed__3;
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_apply_2(x_2, x_11, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instReprExcept___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instToStringString___closed__0 = _init_l_instToStringString___closed__0();
lean_mark_persistent(l_instToStringString___closed__0);
l_instToStringString = _init_l_instToStringString();
lean_mark_persistent(l_instToStringString);
l_instToStringRaw___closed__0 = _init_l_instToStringRaw___closed__0();
lean_mark_persistent(l_instToStringRaw___closed__0);
l_instToStringRaw = _init_l_instToStringRaw();
lean_mark_persistent(l_instToStringRaw);
l_instToStringChar___lam__0___closed__0 = _init_l_instToStringChar___lam__0___closed__0();
lean_mark_persistent(l_instToStringChar___lam__0___closed__0);
l_instToStringChar___closed__0 = _init_l_instToStringChar___closed__0();
lean_mark_persistent(l_instToStringChar___closed__0);
l_instToStringChar = _init_l_instToStringChar();
lean_mark_persistent(l_instToStringChar);
l_instToStringBool___lam__0___closed__0 = _init_l_instToStringBool___lam__0___closed__0();
lean_mark_persistent(l_instToStringBool___lam__0___closed__0);
l_instToStringBool___lam__0___closed__1 = _init_l_instToStringBool___lam__0___closed__1();
lean_mark_persistent(l_instToStringBool___lam__0___closed__1);
l_instToStringBool___closed__0 = _init_l_instToStringBool___closed__0();
lean_mark_persistent(l_instToStringBool___closed__0);
l_instToStringBool = _init_l_instToStringBool();
lean_mark_persistent(l_instToStringBool);
l_instToStringDecidable___closed__0 = _init_l_instToStringDecidable___closed__0();
lean_mark_persistent(l_instToStringDecidable___closed__0);
l_List_toString___redArg___lam__0___closed__0 = _init_l_List_toString___redArg___lam__0___closed__0();
lean_mark_persistent(l_List_toString___redArg___lam__0___closed__0);
l_List_toString___redArg___closed__0 = _init_l_List_toString___redArg___closed__0();
lean_mark_persistent(l_List_toString___redArg___closed__0);
l_List_toString___redArg___closed__1 = _init_l_List_toString___redArg___closed__1();
lean_mark_persistent(l_List_toString___redArg___closed__1);
l_List_toString___redArg___closed__2 = _init_l_List_toString___redArg___closed__2();
lean_mark_persistent(l_List_toString___redArg___closed__2);
l_instToStringPUnit___lam__0___closed__0 = _init_l_instToStringPUnit___lam__0___closed__0();
lean_mark_persistent(l_instToStringPUnit___lam__0___closed__0);
l_instToStringPUnit___closed__0 = _init_l_instToStringPUnit___closed__0();
lean_mark_persistent(l_instToStringPUnit___closed__0);
l_instToStringPUnit = _init_l_instToStringPUnit();
lean_mark_persistent(l_instToStringPUnit);
l_instToStringUnit = _init_l_instToStringUnit();
lean_mark_persistent(l_instToStringUnit);
l_instToStringNat___closed__0 = _init_l_instToStringNat___closed__0();
lean_mark_persistent(l_instToStringNat___closed__0);
l_instToStringNat = _init_l_instToStringNat();
lean_mark_persistent(l_instToStringNat);
l_instToStringRaw__1 = _init_l_instToStringRaw__1();
lean_mark_persistent(l_instToStringRaw__1);
l_instToStringInt___lam__0___closed__0 = _init_l_instToStringInt___lam__0___closed__0();
lean_mark_persistent(l_instToStringInt___lam__0___closed__0);
l_instToStringInt___lam__0___closed__1 = _init_l_instToStringInt___lam__0___closed__1();
lean_mark_persistent(l_instToStringInt___lam__0___closed__1);
l_instToStringInt___closed__0 = _init_l_instToStringInt___closed__0();
lean_mark_persistent(l_instToStringInt___closed__0);
l_instToStringInt = _init_l_instToStringInt();
lean_mark_persistent(l_instToStringInt);
l_instToStringUInt8___closed__0 = _init_l_instToStringUInt8___closed__0();
lean_mark_persistent(l_instToStringUInt8___closed__0);
l_instToStringUInt8 = _init_l_instToStringUInt8();
lean_mark_persistent(l_instToStringUInt8);
l_instToStringUInt16___closed__0 = _init_l_instToStringUInt16___closed__0();
lean_mark_persistent(l_instToStringUInt16___closed__0);
l_instToStringUInt16 = _init_l_instToStringUInt16();
lean_mark_persistent(l_instToStringUInt16);
l_instToStringUInt32___closed__0 = _init_l_instToStringUInt32___closed__0();
lean_mark_persistent(l_instToStringUInt32___closed__0);
l_instToStringUInt32 = _init_l_instToStringUInt32();
lean_mark_persistent(l_instToStringUInt32);
l_instToStringUInt64___closed__0 = _init_l_instToStringUInt64___closed__0();
lean_mark_persistent(l_instToStringUInt64___closed__0);
l_instToStringUInt64 = _init_l_instToStringUInt64();
lean_mark_persistent(l_instToStringUInt64);
l_instToStringUSize___closed__0 = _init_l_instToStringUSize___closed__0();
lean_mark_persistent(l_instToStringUSize___closed__0);
l_instToStringUSize = _init_l_instToStringUSize();
lean_mark_persistent(l_instToStringUSize);
l_instToStringFormat___closed__0 = _init_l_instToStringFormat___closed__0();
lean_mark_persistent(l_instToStringFormat___closed__0);
l_instToStringFormat = _init_l_instToStringFormat();
lean_mark_persistent(l_instToStringFormat);
l_addParenHeuristic___closed__0 = _init_l_addParenHeuristic___closed__0();
lean_mark_persistent(l_addParenHeuristic___closed__0);
l_addParenHeuristic___closed__1 = _init_l_addParenHeuristic___closed__1();
lean_mark_persistent(l_addParenHeuristic___closed__1);
l_addParenHeuristic___closed__2 = _init_l_addParenHeuristic___closed__2();
lean_mark_persistent(l_addParenHeuristic___closed__2);
l_addParenHeuristic___closed__3 = _init_l_addParenHeuristic___closed__3();
lean_mark_persistent(l_addParenHeuristic___closed__3);
l_addParenHeuristic___closed__4 = _init_l_addParenHeuristic___closed__4();
lean_mark_persistent(l_addParenHeuristic___closed__4);
l_instToStringOption___redArg___lam__0___closed__0 = _init_l_instToStringOption___redArg___lam__0___closed__0();
lean_mark_persistent(l_instToStringOption___redArg___lam__0___closed__0);
l_instToStringOption___redArg___lam__0___closed__1 = _init_l_instToStringOption___redArg___lam__0___closed__1();
lean_mark_persistent(l_instToStringOption___redArg___lam__0___closed__1);
l_instToStringSum___redArg___lam__0___closed__0 = _init_l_instToStringSum___redArg___lam__0___closed__0();
lean_mark_persistent(l_instToStringSum___redArg___lam__0___closed__0);
l_instToStringSum___redArg___lam__0___closed__1 = _init_l_instToStringSum___redArg___lam__0___closed__1();
lean_mark_persistent(l_instToStringSum___redArg___lam__0___closed__1);
l_instToStringSigma___redArg___lam__0___closed__0 = _init_l_instToStringSigma___redArg___lam__0___closed__0();
lean_mark_persistent(l_instToStringSigma___redArg___lam__0___closed__0);
l_instToStringSigma___redArg___lam__0___closed__1 = _init_l_instToStringSigma___redArg___lam__0___closed__1();
lean_mark_persistent(l_instToStringSigma___redArg___lam__0___closed__1);
l_instToStringExcept___redArg___lam__0___closed__0 = _init_l_instToStringExcept___redArg___lam__0___closed__0();
lean_mark_persistent(l_instToStringExcept___redArg___lam__0___closed__0);
l_instToStringExcept___redArg___lam__0___closed__1 = _init_l_instToStringExcept___redArg___lam__0___closed__1();
lean_mark_persistent(l_instToStringExcept___redArg___lam__0___closed__1);
l_instReprExcept___redArg___lam__0___closed__0 = _init_l_instReprExcept___redArg___lam__0___closed__0();
lean_mark_persistent(l_instReprExcept___redArg___lam__0___closed__0);
l_instReprExcept___redArg___lam__0___closed__1 = _init_l_instReprExcept___redArg___lam__0___closed__1();
lean_mark_persistent(l_instReprExcept___redArg___lam__0___closed__1);
l_instReprExcept___redArg___lam__0___closed__2 = _init_l_instReprExcept___redArg___lam__0___closed__2();
lean_mark_persistent(l_instReprExcept___redArg___lam__0___closed__2);
l_instReprExcept___redArg___lam__0___closed__3 = _init_l_instReprExcept___redArg___lam__0___closed__3();
lean_mark_persistent(l_instReprExcept___redArg___lam__0___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
