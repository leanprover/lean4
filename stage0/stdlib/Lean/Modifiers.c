// Lean compiler output
// Module: Lean.Modifiers
// Imports: Init Lean.Environment
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
LEAN_EXPORT uint8_t lean_is_protected(lean_object*, lean_object*);
static lean_object* l_Lean_protectedExt___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* lean_private_prefix(lean_object*);
static lean_object* l_Lean_protectedExt___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_protectedExt___closed__5;
LEAN_EXPORT lean_object* l_Lean_privateHeader;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1;
LEAN_EXPORT lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivateNameFromImportedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux(lean_object*);
LEAN_EXPORT uint8_t lean_is_private_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2;
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object*);
static lean_object* l_Lean_protectedExt___closed__6;
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_add_protected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt;
static lean_object* l_Lean_protectedExt___elambda__4___rarg___closed__3;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_protectedExt___closed__7;
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__2(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateNameExport___boxed(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__2___boxed(lean_object*);
static lean_object* l_Lean_protectedExt___elambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__4___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProtected___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__1(lean_object*);
static lean_object* l_Lean_privateHeader___closed__2;
LEAN_EXPORT lean_object* l_Lean_isPrivateNameFromImportedModule___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__4(lean_object*, lean_object*);
static lean_object* l_Lean_protectedExt___closed__4;
static lean_object* l_Lean_privateHeader___closed__1;
static uint32_t l_Lean_protectedExt___elambda__4___rarg___closed__1;
static lean_object* l_Lean_protectedExt___closed__2;
static lean_object* l_Lean_protectedExt___elambda__4___rarg___closed__2;
static lean_object* _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_protectedExt___elambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__2___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static uint32_t _init_l_Lean_protectedExt___elambda__4___rarg___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_protectedExt___elambda__4___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_protectedExt___elambda__4___rarg___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_protectedExt___elambda__4___rarg___closed__1;
x_3 = l_Lean_protectedExt___elambda__4___rarg___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_protectedExt___elambda__4___rarg___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_protectedExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_protectedExt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_protectedExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_protectedExt___closed__3;
x_4 = l_Lean_protectedExt___closed__4;
x_5 = l_Lean_protectedExt___closed__5;
x_6 = l_Lean_protectedExt___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_protectedExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_protectedExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_protectedExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_add_protected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_is_protected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isProtected___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_protected(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_privateHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private");
return x_1;
}
}
static lean_object* _init_l_Lean_privateHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_privateHeader___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_privateHeader() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_privateHeader___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_environment_main_module(x_1);
x_4 = l_Lean_privateHeader;
x_5 = l_Lean_Name_append(x_4, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_name_mk_numeral(x_5, x_6);
x_8 = l_Lean_Name_append(x_7, x_2);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_privateHeader;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
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
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Modifiers_0__Lean_privateToUserNameAux(x_2);
x_5 = lean_name_mk_string(x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
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
x_4 = l___private_Lean_Modifiers_0__Lean_privateToUserNameAux(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivateNameFromImportedModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_private_to_user_name(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_mkPrivateName(x_1, x_5);
x_7 = lean_name_eq(x_6, x_2);
lean_dec(x_2);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivateNameFromImportedModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isPrivateNameFromImportedModule(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Modifiers_0__Lean_privatePrefixAux(x_1);
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
x_4 = l___private_Lean_Modifiers_0__Lean_privatePrefixAux(x_1);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Modifiers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2);
l_Lean_protectedExt___elambda__2___closed__1 = _init_l_Lean_protectedExt___elambda__2___closed__1();
lean_mark_persistent(l_Lean_protectedExt___elambda__2___closed__1);
l_Lean_protectedExt___elambda__4___rarg___closed__1 = _init_l_Lean_protectedExt___elambda__4___rarg___closed__1();
l_Lean_protectedExt___elambda__4___rarg___closed__2 = _init_l_Lean_protectedExt___elambda__4___rarg___closed__2();
lean_mark_persistent(l_Lean_protectedExt___elambda__4___rarg___closed__2);
l_Lean_protectedExt___elambda__4___rarg___closed__3 = _init_l_Lean_protectedExt___elambda__4___rarg___closed__3();
lean_mark_persistent(l_Lean_protectedExt___elambda__4___rarg___closed__3);
l_Lean_protectedExt___closed__1 = _init_l_Lean_protectedExt___closed__1();
lean_mark_persistent(l_Lean_protectedExt___closed__1);
l_Lean_protectedExt___closed__2 = _init_l_Lean_protectedExt___closed__2();
lean_mark_persistent(l_Lean_protectedExt___closed__2);
l_Lean_protectedExt___closed__3 = _init_l_Lean_protectedExt___closed__3();
lean_mark_persistent(l_Lean_protectedExt___closed__3);
l_Lean_protectedExt___closed__4 = _init_l_Lean_protectedExt___closed__4();
lean_mark_persistent(l_Lean_protectedExt___closed__4);
l_Lean_protectedExt___closed__5 = _init_l_Lean_protectedExt___closed__5();
lean_mark_persistent(l_Lean_protectedExt___closed__5);
l_Lean_protectedExt___closed__6 = _init_l_Lean_protectedExt___closed__6();
lean_mark_persistent(l_Lean_protectedExt___closed__6);
l_Lean_protectedExt___closed__7 = _init_l_Lean_protectedExt___closed__7();
lean_mark_persistent(l_Lean_protectedExt___closed__7);
res = l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_protectedExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_protectedExt);
lean_dec_ref(res);
l_Lean_privateHeader___closed__1 = _init_l_Lean_privateHeader___closed__1();
lean_mark_persistent(l_Lean_privateHeader___closed__1);
l_Lean_privateHeader___closed__2 = _init_l_Lean_privateHeader___closed__2();
lean_mark_persistent(l_Lean_privateHeader___closed__2);
l_Lean_privateHeader = _init_l_Lean_privateHeader();
lean_mark_persistent(l_Lean_privateHeader);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
