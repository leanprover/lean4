// Lean compiler output
// Module: Init.Data.FloatArray.Basic
// Imports: Init.Data.Array.Basic Init.Data.Float Init.Data.Option.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_float_array_size(lean_object*);
lean_object* l_FloatArray_get_x3f(lean_object*, lean_object*);
lean_object* l_List_toFloatArray(lean_object*);
lean_object* l_FloatArray_toListAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_FloatArray_HasToString___boxed(lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_List_toStringAux___main___at_FloatArray_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_FloatArray_push___boxed(lean_object*, lean_object*);
lean_object* lean_float_array_push(lean_object*, double);
lean_object* l_FloatArray_get___boxed(lean_object*, lean_object*);
lean_object* l_FloatArray_size___boxed(lean_object*);
lean_object* l_FloatArray_toListAux(lean_object*, lean_object*, lean_object*);
lean_object* l_FloatArray_toList___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_FloatArray_toList(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* lean_float_array_data(lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_FloatArray_toListAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_FloatArray_empty___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_FloatArray_toListAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toFloatArrayAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_FloatArray_set___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_FloatArray_empty;
lean_object* l_FloatArray_isEmpty___boxed(lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_FloatArray_mk___boxed(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
double lean_float_array_fget(lean_object*, lean_object*);
lean_object* lean_float_array_mk(lean_object*);
lean_object* l_FloatArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_FloatArray_isEmpty(lean_object*);
lean_object* l_FloatArray_get_x21___boxed(lean_object*, lean_object*);
lean_object* l_FloatArray_mkEmpty___boxed(lean_object*);
lean_object* lean_float_array_set(lean_object*, lean_object*, double);
lean_object* l_List_toStringAux___main___at_FloatArray_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_List_toString___at_FloatArray_HasToString___spec__1(lean_object*);
lean_object* lean_mk_empty_float_array(lean_object*);
lean_object* l_FloatArray_get_x3f___boxed(lean_object*, lean_object*);
double lean_float_array_get(lean_object*, lean_object*);
lean_object* lean_float_array_fset(lean_object*, lean_object*, double);
lean_object* l_FloatArray_Inhabited;
lean_object* l_FloatArray_data___boxed(lean_object*);
lean_object* l_List_toFloatArrayAux(lean_object*, lean_object*);
lean_object* l_FloatArray_HasToString(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_FloatArray_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_float_array_mk(x_1);
return x_2;
}
}
lean_object* l_FloatArray_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_float_array_data(x_1);
return x_2;
}
}
lean_object* l_FloatArray_mkEmpty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_empty_float_array(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_FloatArray_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_float_array(x_1);
return x_2;
}
}
lean_object* _init_l_FloatArray_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_FloatArray_empty___closed__1;
return x_1;
}
}
lean_object* _init_l_FloatArray_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_FloatArray_empty;
return x_1;
}
}
lean_object* l_FloatArray_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = lean_unbox_float(x_2);
lean_dec(x_2);
x_4 = lean_float_array_push(x_1, x_3);
return x_4;
}
}
lean_object* l_FloatArray_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_float_array_size(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_FloatArray_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = lean_float_array_fget(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_FloatArray_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = lean_float_array_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_FloatArray_get_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_float_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
double x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_float_array_fget(x_1, x_2);
x_7 = lean_box_float(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
lean_object* l_FloatArray_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_FloatArray_get_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_FloatArray_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
double x_4; lean_object* x_5; 
x_4 = lean_unbox_float(x_3);
lean_dec(x_3);
x_5 = lean_float_array_fset(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_FloatArray_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
double x_4; lean_object* x_5; 
x_4 = lean_unbox_float(x_3);
lean_dec(x_3);
x_5 = lean_float_array_set(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_FloatArray_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_float_array_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_FloatArray_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_FloatArray_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_FloatArray_toListAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_float_array_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_List_reverse___rarg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; double x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lean_float_array_get(x_1, x_2);
lean_dec(x_2);
x_10 = lean_box_float(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
}
lean_object* l_FloatArray_toListAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FloatArray_toListAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_FloatArray_toListAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FloatArray_toListAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_FloatArray_toListAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FloatArray_toListAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_FloatArray_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_FloatArray_toListAux___main(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_FloatArray_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_FloatArray_toList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_toFloatArrayAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; double x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unbox_float(x_3);
lean_dec(x_3);
x_6 = lean_float_array_push(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
lean_object* l_List_toFloatArrayAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_toFloatArrayAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toFloatArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_FloatArray_empty;
x_3 = l_List_toFloatArrayAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_FloatArray_HasToString___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; double x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox_float(x_4);
lean_dec(x_4);
x_7 = lean_float_to_string(x_6);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toStringAux___main___at_FloatArray_HasToString___spec__2(x_1, x_5);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; double x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_unbox_float(x_13);
lean_dec(x_13);
x_16 = lean_float_to_string(x_15);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_FloatArray_HasToString___spec__2(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString___at_FloatArray_HasToString___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_FloatArray_HasToString___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_FloatArray_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_FloatArray_toList(x_1);
x_3 = l_List_toString___at_FloatArray_HasToString___spec__1(x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_FloatArray_HasToString___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_FloatArray_HasToString___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_FloatArray_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_FloatArray_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_Float(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_FloatArray_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_FloatArray_empty___closed__1 = _init_l_FloatArray_empty___closed__1();
lean_mark_persistent(l_FloatArray_empty___closed__1);
l_FloatArray_empty = _init_l_FloatArray_empty();
lean_mark_persistent(l_FloatArray_empty);
l_FloatArray_Inhabited = _init_l_FloatArray_Inhabited();
lean_mark_persistent(l_FloatArray_Inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
