// Lean compiler output
// Module: Lean.Modifiers
// Imports: Lean.EnvExtension Lean.PrivateName
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
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Modifiers___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_isPrivateNameFromImportedModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addProtected(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_privateHeader;
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isProtected(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Modifiers___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Modifiers___hyg_3_;
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivateNameFromImportedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt;
static lean_object* l_Lean_addProtected___closed__0;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Modifiers___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Modifiers___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("protectedExt", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Modifiers___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Modifiers___hyg_3_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Modifiers___hyg_3_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Modifiers___hyg_3_;
x_3 = lean_box(2);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_mkTagDeclarationExtension(x_2, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addProtected___closed__0() {
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
x_3 = l_Lean_addProtected___closed__0;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isProtected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_addProtected___closed__0;
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
x_3 = l_Lean_privateHeader;
x_4 = l_Lean_Environment_mainModule(x_1);
x_5 = l_Lean_Name_append(x_3, x_4);
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
lean_object* x_4; uint8_t x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_mkPrivateName(x_1, x_6);
x_8 = lean_name_eq(x_7, x_2);
lean_dec(x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
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
lean_object* initialize_Lean_EnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrivateName(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Modifiers(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Modifiers___hyg_3_ = _init_l_Lean_initFn___closed__0____x40_Lean_Modifiers___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Modifiers___hyg_3_);
l_Lean_initFn___closed__1____x40_Lean_Modifiers___hyg_3_ = _init_l_Lean_initFn___closed__1____x40_Lean_Modifiers___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Modifiers___hyg_3_);
l_Lean_initFn___closed__2____x40_Lean_Modifiers___hyg_3_ = _init_l_Lean_initFn___closed__2____x40_Lean_Modifiers___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Modifiers___hyg_3_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Modifiers___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_protectedExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_protectedExt);
lean_dec_ref(res);
}l_Lean_addProtected___closed__0 = _init_l_Lean_addProtected___closed__0();
lean_mark_persistent(l_Lean_addProtected___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
