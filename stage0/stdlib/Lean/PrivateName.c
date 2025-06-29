// Lean compiler output
// Module: Lean.PrivateName
// Imports: Init.Notation Init.Data.Option.Coe
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
LEAN_EXPORT lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object*);
static lean_object* l_Lean_privateHeader___closed__1;
LEAN_EXPORT uint8_t lean_is_private_name(lean_object*);
LEAN_EXPORT lean_object* lean_private_prefix(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_privateHeader;
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object*);
static lean_object* l_Lean_privateHeader___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateNameCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateNameExport___boxed(lean_object*);
static lean_object* _init_l_Lean_privateHeader___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_privateHeader___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_privateHeader___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_privateHeader() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_privateHeader___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPrivateNameCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_privateHeader;
x_4 = l_Lean_Name_append(x_3, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Name_num___override(x_4, x_5);
x_7 = l_Lean_Name_append(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_privateHeader;
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
x_1 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPrivateName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_is_private_name(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivateNameExport___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_private_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix_go(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_privateHeader;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
x_1 = x_4;
goto _start;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPrivatePrefix_go(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l_Lean_isPrivatePrefix_go(x_2);
return x_6;
}
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPrivatePrefix(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(x_2);
x_5 = l_Lean_Name_str___override(x_4, x_3);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_isPrivatePrefix(x_1);
lean_dec(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(x_6);
x_10 = l_Lean_Name_num___override(x_9, x_7);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_private_to_user_name(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_private_prefix(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(x_1);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
lean_object* initialize_Init_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrivateName(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_privateHeader___closed__0 = _init_l_Lean_privateHeader___closed__0();
lean_mark_persistent(l_Lean_privateHeader___closed__0);
l_Lean_privateHeader___closed__1 = _init_l_Lean_privateHeader___closed__1();
lean_mark_persistent(l_Lean_privateHeader___closed__1);
l_Lean_privateHeader = _init_l_Lean_privateHeader();
lean_mark_persistent(l_Lean_privateHeader);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
