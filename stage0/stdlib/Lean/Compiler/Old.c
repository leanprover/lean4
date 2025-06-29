// Lean compiler output
// Module: Lean.Compiler.Old
// Imports: Lean.Environment
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
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__0;
LEAN_EXPORT lean_object* lean_mk_eager_lambda_lifting_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__0;
LEAN_EXPORT uint8_t l_Lean_Compiler_checkIsDefinition___lam__1(uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_checkIsDefinition___lam__0(lean_object*);
LEAN_EXPORT lean_object* lean_is_unsafe_rec_name(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__1;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__2;
lean_object* l_List_mapTR_loop___at___Lean_Declaration_getTopLevelNames_spec__0(lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_unsafe_rec_name(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition___lam__0___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
LEAN_EXPORT uint8_t lean_is_eager_lambda_lifting_name(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
static lean_object* _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elambda_", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_eager_lambda_lifting_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
x_4 = l_Nat_reprFast(x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec(x_4);
x_6 = l_Lean_Name_str___override(x_1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elambda", 8, 8);
return x_1;
}
}
LEAN_EXPORT uint8_t lean_is_eager_lambda_lifting_name(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
x_7 = l_String_isPrefixOf(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
lean_dec(x_4);
return x_7;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_eager_lambda_lifting_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_List_mapTR_loop___at___Lean_Declaration_getTopLevelNames_spec__0(x_17, x_18);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_box(0);
return x_20;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_checkIsDefinition___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_checkIsDefinition___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration is not a definition '", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_2);
x_7 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_checkIsDefinition___lam__0___boxed), 1, 0);
x_9 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_2, x_11, x_8);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
lean_dec(x_18);
x_20 = lean_box(x_19);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_free_object(x_7);
lean_dec(x_2);
goto block_4;
}
case 3:
{
lean_free_object(x_7);
lean_dec(x_2);
goto block_4;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_checkIsDefinition___lam__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_5);
x_22 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Name_toString(x_2, x_24, x_21);
x_26 = lean_string_append(x_22, x_25);
lean_dec(x_25);
x_27 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_28);
return x_7;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*3);
lean_dec(x_29);
x_31 = lean_box(x_30);
switch (lean_obj_tag(x_31)) {
case 0:
{
lean_dec(x_2);
goto block_4;
}
case 3:
{
lean_dec(x_2);
goto block_4;
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_checkIsDefinition___lam__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_5);
x_33 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_34 = lean_box(1);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Name_toString(x_2, x_35, x_32);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
block_4:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_checkIsDefinition___closed__0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_checkIsDefinition___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_checkIsDefinition___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_mkUnsafeRecName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_unsafe_rec", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_unsafe_rec_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkUnsafeRecName___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_is_unsafe_rec_name(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Compiler_mkUnsafeRecName___closed__0;
x_5 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Old(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0 = _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0();
lean_mark_persistent(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0);
l_Lean_Compiler_isEagerLambdaLiftingName___closed__0 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__0();
lean_mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0);
l_Lean_Compiler_checkIsDefinition___closed__0 = _init_l_Lean_Compiler_checkIsDefinition___closed__0();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__0);
l_Lean_Compiler_checkIsDefinition___closed__1 = _init_l_Lean_Compiler_checkIsDefinition___closed__1();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__2 = _init_l_Lean_Compiler_checkIsDefinition___closed__2();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__2);
l_Lean_Compiler_checkIsDefinition___closed__3 = _init_l_Lean_Compiler_checkIsDefinition___closed__3();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__3);
l_Lean_Compiler_mkUnsafeRecName___closed__0 = _init_l_Lean_Compiler_mkUnsafeRecName___closed__0();
lean_mark_persistent(l_Lean_Compiler_mkUnsafeRecName___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
