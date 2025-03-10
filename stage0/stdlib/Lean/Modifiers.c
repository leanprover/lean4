// Lean compiler output
// Module: Lean.Modifiers
// Imports: Lean.Environment Lean.PrivateName
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
LEAN_EXPORT lean_object* l_Lean_isProtected___boxed(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateNameFromImportedModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addProtected(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__3;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_privateHeader;
lean_object* l_Lean_privateToUserName(lean_object*);
static lean_object* l_Lean_addProtected___closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isProtected(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivateNameFromImportedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1;
LEAN_EXPORT lean_object* l_Lean_protectedExt;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("protectedExt", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__3;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addProtected___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_protectedExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addProtected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_addProtected___closed__1;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isProtected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_addProtected___closed__1;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isProtected___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isProtected(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_Environment_mainModule(x_1);
x_4 = l_Lean_privateHeader;
x_5 = l_Lean_Name_append(x_4, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Name_num___override(x_5, x_6);
x_8 = l_Lean_privateToUserName(x_2);
x_9 = l_Lean_Name_append(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPrivateName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPrivateName(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrivateName(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Modifiers(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Modifiers___hyg_3____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_protectedExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_protectedExt);
lean_dec_ref(res);
}l_Lean_addProtected___closed__1 = _init_l_Lean_addProtected___closed__1();
lean_mark_persistent(l_Lean_addProtected___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
