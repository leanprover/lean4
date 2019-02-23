// Lean compiler output
// Module: init.data.char.basic
// Imports: init.data.uint
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
uint8 l_char_is__whitespace(uint32);
obj* l_char_is__upper___boxed(obj*);
uint8 l_char_is__lower(uint32);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint32 l_char_to__lower(uint32);
obj* l_char_is__digit___boxed(obj*);
obj* l_char_dec__lt___boxed(obj*, obj*);
uint8 l_char_is__digit(uint32);
uint32 l_char_of__nat(obj*);
obj* l_char_has__lt;
obj* l_char_of__nat___boxed(obj*);
obj* l_char_is__alphanum___boxed(obj*);
uint8 l_char_is__upper(uint32);
uint8 l_char_is__alpha(uint32);
obj* l_char_to__lower___boxed(obj*);
obj* l_char_is__whitespace___boxed(obj*);
obj* l_char_to__nat___boxed(obj*);
obj* l_char_dec__le___boxed(obj*, obj*);
obj* l_char_has__sizeof___boxed(obj*);
obj* l_char_lt;
uint32 l_char_inhabited;
obj* l_char_has__sizeof(uint32);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
uint8 l_char_dec__lt(uint32, uint32);
obj* l_char_is__lower___boxed(obj*);
obj* l_char_decidable__eq___boxed(obj*, obj*);
obj* l_char_inhabited___boxed;
uint8 l_char_dec__le(uint32, uint32);
obj* l_char_has__le;
uint8 l_char_is__alphanum(uint32);
obj* l_char_le;
uint8 l_char_decidable__eq(uint32, uint32);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_char_to__nat(uint32);
obj* l_is__valid__char;
obj* l_char_is__alpha___boxed(obj*);
obj* _init_l_is__valid__char() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_char_has__sizeof(uint32 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_char_has__sizeof___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_has__sizeof(x_1);
return x_2;
}
}
obj* _init_l_char_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_char_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_char_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_char_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_char_dec__lt(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_char_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_char_dec__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_char_dec__le(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_char_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_char_dec__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint32 l_char_of__nat(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; uint8 x_3; 
x_1 = lean::uint32_of_nat(x_0);
x_2 = 55296;
x_3 = x_1 < x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 57343;
x_5 = x_4 < x_1;
if (x_5 == 0)
{
uint32 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint32 x_7; uint8 x_8; 
x_7 = 1114112;
x_8 = x_1 < x_7;
if (x_8 == 0)
{
uint32 x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
obj* l_char_of__nat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_char_of__nat(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_char_to__nat(uint32 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_char_to__nat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__nat(x_1);
return x_2;
}
}
uint8 l_char_decidable__eq(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_char_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_char_decidable__eq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint32 _init_l_char_inhabited() {
_start:
{
uint32 x_0; 
x_0 = 65;
return x_0;
}
}
obj* _init_l_char_inhabited___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_char_inhabited;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint8 l_char_is__whitespace(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 32;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint32 x_3; uint8 x_4; 
x_3 = 9;
x_4 = x_0 == x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = 10;
x_6 = x_0 == x_5;
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
}
obj* l_char_is__whitespace___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__whitespace(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__upper(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 65;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 90;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_char_is__upper___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__upper(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__lower(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 97;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 122;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_char_is__lower___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__lower(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__alpha(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_char_is__upper(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = l_char_is__lower(x_0);
return x_2;
}
else
{
return x_1;
}
}
}
obj* l_char_is__alpha___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__alpha(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__digit(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 48;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 57;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_char_is__digit___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__digit(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__alphanum(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_char_is__alpha(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = l_char_is__digit(x_0);
return x_2;
}
else
{
return x_1;
}
}
}
obj* l_char_is__alphanum___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__alphanum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 l_char_to__lower(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = lean::mk_nat_obj(65u);
x_3 = lean::nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(90u);
x_6 = lean::nat_dec_le(x_1, x_5);
if (x_6 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; 
x_8 = lean::mk_nat_obj(32u);
x_9 = lean::nat_add(x_1, x_8);
lean::dec(x_1);
x_11 = l_char_of__nat(x_9);
lean::dec(x_9);
return x_11;
}
}
}
}
obj* l_char_to__lower___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__lower(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
void initialize_init_data_uint();
static bool _G_initialized = false;
void initialize_init_data_char_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_uint();
 l_is__valid__char = _init_l_is__valid__char();
lean::mark_persistent(l_is__valid__char);
 l_char_lt = _init_l_char_lt();
lean::mark_persistent(l_char_lt);
 l_char_le = _init_l_char_le();
lean::mark_persistent(l_char_le);
 l_char_has__lt = _init_l_char_has__lt();
lean::mark_persistent(l_char_has__lt);
 l_char_has__le = _init_l_char_has__le();
lean::mark_persistent(l_char_has__le);
 l_char_inhabited = _init_l_char_inhabited();
 l_char_inhabited___boxed = _init_l_char_inhabited___boxed();
lean::mark_persistent(l_char_inhabited___boxed);
}
