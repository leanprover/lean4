// Lean compiler output
// Module: Lake.Config.ConfigTarget
// Imports: Lake.Config.Package
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
static lean_object* l_Lake_Package_configTargets___closed__6;
static lean_object* l_Lake_Package_configTargets___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__9;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__0;
static lean_object* l_Lake_Package_configTargets___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget(lean_object*, lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__10;
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableConfigTarget___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets(lean_object*, lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__8;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__3;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__5;
static lean_object* l_Lake_Package_configTargets___closed__4;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__1;
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instBEqConfigTarget___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableConfigTarget___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Name_hash___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instHashableConfigTarget___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_instHashableConfigTarget___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instHashableConfigTarget(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqConfigTarget___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instBEqConfigTarget___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instBEqConfigTarget___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instBEqConfigTarget(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PConfigDecl_mkConfigTarget(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_name_eq(x_6, x_1);
if (x_8 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_7);
x_10 = lean_array_push(x_3, x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_configTargets___closed__2;
x_2 = l_Lake_Package_configTargets___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_Package_configTargets___closed__6;
x_2 = l_Lake_Package_configTargets___closed__5;
x_3 = l_Lake_Package_configTargets___closed__4;
x_4 = l_Lake_Package_configTargets___closed__3;
x_5 = l_Lake_Package_configTargets___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_configTargets___closed__7;
x_2 = l_Lake_Package_configTargets___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 10);
lean_inc_ref(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lake_Package_configTargets___closed__0;
x_6 = lean_array_get_size(x_3);
x_7 = l_Lake_Package_configTargets___closed__10;
x_8 = lean_nat_dec_lt(x_4, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lake_Package_configTargets___lam__0___boxed), 4, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = 0;
x_12 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_10, x_3, x_11, x_12, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_configTargets___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Package_findTargetDecl_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_8);
lean_free_object(x_4);
lean_dec_ref(x_3);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 3);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_name_eq(x_16, x_1);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_3);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Package_findConfigTarget_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_ConfigTarget(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_configTargets___closed__0 = _init_l_Lake_Package_configTargets___closed__0();
lean_mark_persistent(l_Lake_Package_configTargets___closed__0);
l_Lake_Package_configTargets___closed__1 = _init_l_Lake_Package_configTargets___closed__1();
lean_mark_persistent(l_Lake_Package_configTargets___closed__1);
l_Lake_Package_configTargets___closed__2 = _init_l_Lake_Package_configTargets___closed__2();
lean_mark_persistent(l_Lake_Package_configTargets___closed__2);
l_Lake_Package_configTargets___closed__3 = _init_l_Lake_Package_configTargets___closed__3();
lean_mark_persistent(l_Lake_Package_configTargets___closed__3);
l_Lake_Package_configTargets___closed__4 = _init_l_Lake_Package_configTargets___closed__4();
lean_mark_persistent(l_Lake_Package_configTargets___closed__4);
l_Lake_Package_configTargets___closed__5 = _init_l_Lake_Package_configTargets___closed__5();
lean_mark_persistent(l_Lake_Package_configTargets___closed__5);
l_Lake_Package_configTargets___closed__6 = _init_l_Lake_Package_configTargets___closed__6();
lean_mark_persistent(l_Lake_Package_configTargets___closed__6);
l_Lake_Package_configTargets___closed__7 = _init_l_Lake_Package_configTargets___closed__7();
lean_mark_persistent(l_Lake_Package_configTargets___closed__7);
l_Lake_Package_configTargets___closed__8 = _init_l_Lake_Package_configTargets___closed__8();
lean_mark_persistent(l_Lake_Package_configTargets___closed__8);
l_Lake_Package_configTargets___closed__9 = _init_l_Lake_Package_configTargets___closed__9();
lean_mark_persistent(l_Lake_Package_configTargets___closed__9);
l_Lake_Package_configTargets___closed__10 = _init_l_Lake_Package_configTargets___closed__10();
lean_mark_persistent(l_Lake_Package_configTargets___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
