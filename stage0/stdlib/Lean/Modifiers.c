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
uint8_t lean_is_protected(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___closed__1;
lean_object* l_Lean_protectedExt___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___closed__5;
lean_object* l_Lean_privateHeader;
extern lean_object* l_Array_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_protectedExt___elambda__1___boxed(lean_object*);
lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux(lean_object*);
uint8_t lean_is_private_name(lean_object*);
lean_object* l_Lean_isPrivateName___boxed(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object*);
lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* lean_add_protected(lean_object*, lean_object*);
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* l_Lean_protectedExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isPrivateName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__2(lean_object*);
lean_object* lean_private_prefix(lean_object*);
lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux_match__1(lean_object*);
lean_object* l_Lean_isPrivateName_match__1(lean_object*);
lean_object* l_Lean_isPrivateNameExport___boxed(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_protectedExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux(lean_object*);
lean_object* l_Lean_protectedExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_isProtected___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux___boxed(lean_object*);
lean_object* l_Lean_protectedExt___elambda__1(lean_object*);
lean_object* l_Lean_privateHeader___closed__2;
lean_object* l_Lean_protectedExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___closed__4;
lean_object* l_Lean_privateHeader___closed__1;
lean_object* l_Lean_protectedExt___closed__2;
#define _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("protected");\
__INIT_VAR__ = x_1; goto l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1_end;\
}\
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1_end: ((void) 0);}
#define _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2_end;\
}\
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2_end: ((void) 0);}
lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_protectedExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_protectedExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_protectedExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
#define _init_l_Lean_protectedExt___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__4___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_protectedExt___closed__1_end;\
}\
l_Lean_protectedExt___closed__1_end: ((void) 0);}
#define _init_l_Lean_protectedExt___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__3___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_protectedExt___closed__2_end;\
}\
l_Lean_protectedExt___closed__2_end: ((void) 0);}
#define _init_l_Lean_protectedExt___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__2___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_protectedExt___closed__3_end;\
}\
l_Lean_protectedExt___closed__3_end: ((void) 0);}
#define _init_l_Lean_protectedExt___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__1___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_protectedExt___closed__4_end;\
}\
l_Lean_protectedExt___closed__4_end: ((void) 0);}
#define _init_l_Lean_protectedExt___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; \
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;\
x_2 = lean_box(0);\
x_3 = l_Lean_protectedExt___closed__1;\
x_4 = l_Lean_protectedExt___closed__2;\
x_5 = l_Lean_protectedExt___closed__3;\
x_6 = l_Lean_protectedExt___closed__4;\
x_7 = lean_alloc_ctor(0, 6, 0);\
lean_ctor_set(x_7, 0, x_1);\
lean_ctor_set(x_7, 1, x_2);\
lean_ctor_set(x_7, 2, x_3);\
lean_ctor_set(x_7, 3, x_4);\
lean_ctor_set(x_7, 4, x_5);\
lean_ctor_set(x_7, 5, x_6);\
__INIT_VAR__ = x_7; goto l_Lean_protectedExt___closed__5_end;\
}\
l_Lean_protectedExt___closed__5_end: ((void) 0);}
lean_object* l_Lean_protectedExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_protectedExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_protectedExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_protectedExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_add_protected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t lean_is_protected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_isProtected___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_protected(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
#define _init_l_Lean_privateHeader___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("_private");\
__INIT_VAR__ = x_1; goto l_Lean_privateHeader___closed__1_end;\
}\
l_Lean_privateHeader___closed__1_end: ((void) 0);}
#define _init_l_Lean_privateHeader___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_privateHeader___closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_privateHeader___closed__2_end;\
}\
l_Lean_privateHeader___closed__2_end: ((void) 0);}
#define _init_l_Lean_privateHeader(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_privateHeader___closed__2;\
__INIT_VAR__ = x_1; goto l_Lean_privateHeader_end;\
}\
l_Lean_privateHeader_end: ((void) 0);}
lean_object* l_Lean_mkPrivateName(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_isPrivateName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_4(x_2, x_1, x_6, x_7, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_3(x_3, x_11, x_12, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_isPrivateName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isPrivateName_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_isPrivateName(lean_object* x_1) {
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
lean_object* l_Lean_isPrivateName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPrivateName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_is_private_name(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_isPrivateNameExport___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_private_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Modifiers_0__Lean_privateToUserNameAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Modifiers_0__Lean_privateToUserNameAux(lean_object* x_1) {
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
lean_object* lean_private_to_user_name(lean_object* x_1) {
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
lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux(lean_object* x_1) {
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
lean_object* l___private_Lean_Modifiers_0__Lean_privatePrefixAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Modifiers_0__Lean_privatePrefixAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_private_prefix(lean_object* x_1) {
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
lean_object* initialize_Lean_Modifiers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1);
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1);
_init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2);
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2);
_init_l_Lean_protectedExt___closed__1(l_Lean_protectedExt___closed__1);
lean_mark_persistent(l_Lean_protectedExt___closed__1);
_init_l_Lean_protectedExt___closed__2(l_Lean_protectedExt___closed__2);
lean_mark_persistent(l_Lean_protectedExt___closed__2);
_init_l_Lean_protectedExt___closed__3(l_Lean_protectedExt___closed__3);
lean_mark_persistent(l_Lean_protectedExt___closed__3);
_init_l_Lean_protectedExt___closed__4(l_Lean_protectedExt___closed__4);
lean_mark_persistent(l_Lean_protectedExt___closed__4);
_init_l_Lean_protectedExt___closed__5(l_Lean_protectedExt___closed__5);
lean_mark_persistent(l_Lean_protectedExt___closed__5);
res = l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_protectedExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_protectedExt);
lean_dec_ref(res);
_init_l_Lean_privateHeader___closed__1(l_Lean_privateHeader___closed__1);
lean_mark_persistent(l_Lean_privateHeader___closed__1);
_init_l_Lean_privateHeader___closed__2(l_Lean_privateHeader___closed__2);
lean_mark_persistent(l_Lean_privateHeader___closed__2);
_init_l_Lean_privateHeader(l_Lean_privateHeader);
lean_mark_persistent(l_Lean_privateHeader);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
