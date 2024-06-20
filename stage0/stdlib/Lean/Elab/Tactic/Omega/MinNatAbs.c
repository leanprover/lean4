// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.MinNatAbs
// Imports: Init.BinderPredicates Init.Data.Int.Order Init.Data.List.Lemmas Init.Data.Nat.MinMax Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l_List_nonzeroMinimum(lean_object*);
LEAN_EXPORT lean_object* l_List_minimum_x3f___at_List_nonzeroMinimum___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_minimum_x3f___at_List_nonzeroMinimum___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_maximum_x3f___at_List_maxNatAbs___spec__1(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_List_filter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_List_nonzeroMinimum___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_List_minNatAbs___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_maxNatAbs(lean_object*);
LEAN_EXPORT uint8_t l_List_nonzeroMinimum___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_List_nonzeroMinimum___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_List_nonzeroMinimum___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_List_maxNatAbs___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_List_maxNatAbs___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_nonzeroMinimum___lambda__1___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minNatAbs(lean_object*);
LEAN_EXPORT lean_object* l_List_maximum_x3f___at_List_maxNatAbs___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_List_nonzeroMinimum___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_le(x_1, x_3);
if (x_5 == 0)
{
x_1 = x_3;
x_2 = x_4;
goto _start;
}
else
{
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_minimum_x3f___at_List_nonzeroMinimum___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_foldl___at_List_nonzeroMinimum___spec__2(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_List_nonzeroMinimum___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
x_4 = l_instDecidableNot___rarg(x_3);
return x_4;
}
}
static lean_object* _init_l_List_nonzeroMinimum___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_nonzeroMinimum___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_nonzeroMinimum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_nonzeroMinimum___closed__1;
x_3 = l_List_filter___rarg(x_2, x_1);
x_4 = l_List_minimum_x3f___at_List_nonzeroMinimum___spec__1(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_List_nonzeroMinimum___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_List_nonzeroMinimum___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_minimum_x3f___at_List_nonzeroMinimum___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_minimum_x3f___at_List_nonzeroMinimum___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_nonzeroMinimum___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_nonzeroMinimum___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_map___at_List_minNatAbs___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_abs(x_4);
lean_dec(x_4);
x_7 = l_List_map___at_List_minNatAbs___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_nat_abs(x_8);
lean_dec(x_8);
x_11 = l_List_map___at_List_minNatAbs___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_minNatAbs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_map___at_List_minNatAbs___spec__1(x_1);
x_3 = l_List_nonzeroMinimum(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_List_maxNatAbs___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_le(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
x_1 = x_3;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_maximum_x3f___at_List_maxNatAbs___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_foldl___at_List_maxNatAbs___spec__2(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_maxNatAbs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_map___at_List_minNatAbs___spec__1(x_1);
x_3 = l_List_maximum_x3f___at_List_maxNatAbs___spec__1(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_List_maxNatAbs___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_List_maxNatAbs___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_maximum_x3f___at_List_maxNatAbs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_maximum_x3f___at_List_maxNatAbs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_BinderPredicates(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderPredicates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_nonzeroMinimum___closed__1 = _init_l_List_nonzeroMinimum___closed__1();
lean_mark_persistent(l_List_nonzeroMinimum___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
