// Lean compiler output
// Module: Lean.Data.OpenDecl
// Imports: Init.Meta
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
LEAN_EXPORT uint8_t l_Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45__spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_OpenDecl_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_rootNamespace___closed__0;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToString;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instInhabited;
LEAN_EXPORT uint8_t l_List_beq___at___Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45__spec__0(lean_object*, lean_object*);
uint8_t l_List_beq___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_OpenDecl_instToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_OpenDecl_instToString___lam__0___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rootNamespace;
static lean_object* l_Lean_rootNamespace___closed__1;
static lean_object* l_Lean_OpenDecl_instToString___closed__1;
static lean_object* l_Lean_instBEqOpenDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
static lean_object* l_Lean_OpenDecl_instToString___lam__0___closed__1;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToString___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqOpenDecl;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_OpenDecl_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_List_beq___at___Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45__spec__0(x_4, x_6);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_name_eq(x_11, x_13);
if (x_15 == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_name_eq(x_12, x_14);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45__spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45_(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqOpenDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqOpenDecl____x40_Lean_Data_OpenDecl_3475076167____hygCtx___hyg_45____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqOpenDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqOpenDecl___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_OpenDecl_instInhabited___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OpenDecl_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_OpenDecl_instInhabited___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_OpenDecl_instToString___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" hiding ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_OpenDecl_instToString___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" → ", 5, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToString___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = 1;
x_7 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_4, x_6);
x_8 = lean_box(0);
lean_inc(x_5);
x_9 = l_List_beq___redArg(x_1, x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_OpenDecl_instToString___lam__0___closed__0;
x_11 = l_List_toString___redArg(x_2, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_7, x_12);
lean_dec_ref(x_12);
return x_13;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_2);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = 1;
x_17 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_14, x_16);
x_18 = l_Lean_OpenDecl_instToString___lam__0___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_15, x_16);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
return x_21;
}
}
}
static lean_object* _init_l_Lean_OpenDecl_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_instToString___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_OpenDecl_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_OpenDecl_instToString() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_OpenDecl_instToString___closed__0;
x_2 = l_Lean_OpenDecl_instToString___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_OpenDecl_instToString___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_rootNamespace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_root_", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_rootNamespace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_rootNamespace___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_rootNamespace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_rootNamespace___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_rootNamespace;
x_3 = lean_box(0);
x_4 = l_Lean_Name_replacePrefix(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Meta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instBEqOpenDecl___closed__0 = _init_l_Lean_instBEqOpenDecl___closed__0();
lean_mark_persistent(l_Lean_instBEqOpenDecl___closed__0);
l_Lean_instBEqOpenDecl = _init_l_Lean_instBEqOpenDecl();
lean_mark_persistent(l_Lean_instBEqOpenDecl);
l_Lean_OpenDecl_instInhabited___closed__0 = _init_l_Lean_OpenDecl_instInhabited___closed__0();
lean_mark_persistent(l_Lean_OpenDecl_instInhabited___closed__0);
l_Lean_OpenDecl_instInhabited = _init_l_Lean_OpenDecl_instInhabited();
lean_mark_persistent(l_Lean_OpenDecl_instInhabited);
l_Lean_OpenDecl_instToString___lam__0___closed__0 = _init_l_Lean_OpenDecl_instToString___lam__0___closed__0();
lean_mark_persistent(l_Lean_OpenDecl_instToString___lam__0___closed__0);
l_Lean_OpenDecl_instToString___lam__0___closed__1 = _init_l_Lean_OpenDecl_instToString___lam__0___closed__1();
lean_mark_persistent(l_Lean_OpenDecl_instToString___lam__0___closed__1);
l_Lean_OpenDecl_instToString___closed__0 = _init_l_Lean_OpenDecl_instToString___closed__0();
lean_mark_persistent(l_Lean_OpenDecl_instToString___closed__0);
l_Lean_OpenDecl_instToString___closed__1 = _init_l_Lean_OpenDecl_instToString___closed__1();
lean_mark_persistent(l_Lean_OpenDecl_instToString___closed__1);
l_Lean_OpenDecl_instToString = _init_l_Lean_OpenDecl_instToString();
lean_mark_persistent(l_Lean_OpenDecl_instToString);
l_Lean_rootNamespace___closed__0 = _init_l_Lean_rootNamespace___closed__0();
lean_mark_persistent(l_Lean_rootNamespace___closed__0);
l_Lean_rootNamespace___closed__1 = _init_l_Lean_rootNamespace___closed__1();
lean_mark_persistent(l_Lean_rootNamespace___closed__1);
l_Lean_rootNamespace = _init_l_Lean_rootNamespace();
lean_mark_persistent(l_Lean_rootNamespace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
