// Lean compiler output
// Module: Lean.Compiler.MetaAttr
// Imports: Lean.EnvExtension
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
LEAN_EXPORT lean_object* l_Lean_addMeta(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__4;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Compiler_MetaAttr___hyg_4_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Compiler_MetaAttr___hyg_4_;
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isMeta(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Compiler_MetaAttr___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_MetaAttr___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_getIRPhases_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_get_ir_phases(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__0;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__1;
static lean_object* l_Lean_getIRPhases___closed__1;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__6;
static lean_object* l_Lean_getIRPhases___closed__0;
LEAN_EXPORT uint8_t l_panic___at___Lean_getIRPhases_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isMeta___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getIRPhases___closed__2;
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_addMeta___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getIRPhases___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__2;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
static lean_object* l_panic___at___Lean_getIRPhases_spec__0___closed__3;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_metaExt;
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_MetaAttr___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_MetaAttr___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("metaExt", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Compiler_MetaAttr___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Compiler_MetaAttr___hyg_4_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Compiler_MetaAttr___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_MetaAttr___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Compiler_MetaAttr___hyg_4_;
x_3 = 3;
x_4 = l_Lean_mkTagDeclarationExtension(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_addMeta___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_metaExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addMeta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_addMeta___closed__0;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isMeta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_addMeta___closed__0;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isMeta___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isMeta(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_getIRPhases_spec__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_panic___at___Lean_getIRPhases_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_2 = l_panic___at___Lean_getIRPhases_spec__0___closed__0;
x_3 = l_panic___at___Lean_getIRPhases_spec__0___closed__1;
x_4 = l_panic___at___Lean_getIRPhases_spec__0___closed__2;
x_5 = l_panic___at___Lean_getIRPhases_spec__0___closed__3;
x_6 = l_panic___at___Lean_getIRPhases_spec__0___closed__4;
x_7 = l_panic___at___Lean_getIRPhases_spec__0___closed__5;
x_8 = l_panic___at___Lean_getIRPhases_spec__0___closed__6;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = l_instInhabitedOfMonad___redArg(x_11, x_13);
x_15 = lean_panic_fn(x_14, x_1);
x_16 = lean_unbox(x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_getIRPhases___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(23u);
x_4 = l_Lean_getIRPhases___closed__1;
x_5 = l_Lean_getIRPhases___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t lean_get_ir_phases(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Environment_header(x_1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 4);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = 2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_6);
x_8 = l_Lean_isMeta(x_1, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = l_Lean_isMeta(x_1, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_11, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec_ref(x_6);
x_15 = l_Lean_getIRPhases___closed__3;
x_16 = l_panic___at___Lean_getIRPhases_spec__0(x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_6, x_11);
lean_dec(x_11);
lean_dec_ref(x_6);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec_ref(x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec_ref(x_6);
x_19 = 1;
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_getIRPhases_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_getIRPhases_spec__0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_get_ir_phases(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Compiler_MetaAttr___hyg_4_ = _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_MetaAttr___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Compiler_MetaAttr___hyg_4_);
l_Lean_initFn___closed__1____x40_Lean_Compiler_MetaAttr___hyg_4_ = _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_MetaAttr___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Compiler_MetaAttr___hyg_4_);
l_Lean_initFn___closed__2____x40_Lean_Compiler_MetaAttr___hyg_4_ = _init_l_Lean_initFn___closed__2____x40_Lean_Compiler_MetaAttr___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Compiler_MetaAttr___hyg_4_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_MetaAttr___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_metaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_metaExt);
lean_dec_ref(res);
}l_Lean_addMeta___closed__0 = _init_l_Lean_addMeta___closed__0();
lean_mark_persistent(l_Lean_addMeta___closed__0);
l_panic___at___Lean_getIRPhases_spec__0___closed__0 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__0);
l_panic___at___Lean_getIRPhases_spec__0___closed__1 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__1);
l_panic___at___Lean_getIRPhases_spec__0___closed__2 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__2);
l_panic___at___Lean_getIRPhases_spec__0___closed__3 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__3();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__3);
l_panic___at___Lean_getIRPhases_spec__0___closed__4 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__4();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__4);
l_panic___at___Lean_getIRPhases_spec__0___closed__5 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__5();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__5);
l_panic___at___Lean_getIRPhases_spec__0___closed__6 = _init_l_panic___at___Lean_getIRPhases_spec__0___closed__6();
lean_mark_persistent(l_panic___at___Lean_getIRPhases_spec__0___closed__6);
l_Lean_getIRPhases___closed__0 = _init_l_Lean_getIRPhases___closed__0();
lean_mark_persistent(l_Lean_getIRPhases___closed__0);
l_Lean_getIRPhases___closed__1 = _init_l_Lean_getIRPhases___closed__1();
lean_mark_persistent(l_Lean_getIRPhases___closed__1);
l_Lean_getIRPhases___closed__2 = _init_l_Lean_getIRPhases___closed__2();
lean_mark_persistent(l_Lean_getIRPhases___closed__2);
l_Lean_getIRPhases___closed__3 = _init_l_Lean_getIRPhases___closed__3();
lean_mark_persistent(l_Lean_getIRPhases___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
