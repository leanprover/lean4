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
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableConfigTarget___rarg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_configTargets___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instBEqConfigTarget___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_configTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Package_configTargets___closed__1;
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableConfigTarget___rarg(lean_object* x_1) {
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
x_2 = lean_alloc_closure((void*)(l_Lake_instHashableConfigTarget___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___rarg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_instHashableConfigTarget___rarg(x_1);
lean_dec(x_1);
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
LEAN_EXPORT uint8_t l_Lake_instBEqConfigTarget___rarg(lean_object* x_1, lean_object* x_2) {
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
x_2 = lean_alloc_closure((void*)(l_Lake_instBEqConfigTarget___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instBEqConfigTarget___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_configTargets___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_name_eq(x_12, x_1);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_13);
x_17 = lean_array_push(x_6, x_16);
x_4 = x_10;
x_6 = x_17;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_6;
}
}
}
static lean_object* _init_l_Lake_Package_configTargets___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 9);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = l_Lake_Package_configTargets___closed__1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lake_Package_configTargets___closed__1;
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Lake_Package_configTargets___closed__1;
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_configTargets___spec__1(x_1, x_2, x_3, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_configTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Package_configTargets___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Package_configTargets(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
l_Lake_Package_configTargets___closed__1 = _init_l_Lake_Package_configTargets___closed__1();
lean_mark_persistent(l_Lake_Package_configTargets___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
