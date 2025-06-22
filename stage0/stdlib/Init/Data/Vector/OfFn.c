// Lean compiler output
// Module: Init.Data.Vector.OfFn
// Imports: Init.Data.Vector.Basic Init.Data.Vector.Lemmas Init.Data.Vector.Monadic Init.Data.Array.OfFn
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
static lean_object* l___auto___closed__4____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFnM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__3____x40_Init_Data_Vector_OfFn___hyg_2743_;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__23____x40_Init_Data_Vector_OfFn___hyg_2743_;
LEAN_EXPORT lean_object* l_Vector_ofFnM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__14____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__16____x40_Init_Data_Vector_OfFn___hyg_2743_;
lean_object* l_Array_empty(lean_object*);
static lean_object* l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__6____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__12____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__15____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__17____x40_Init_Data_Vector_OfFn___hyg_2743_;
LEAN_EXPORT lean_object* l_Vector_ofFnM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFnM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__11____x40_Init_Data_Vector_OfFn___hyg_2743_;
LEAN_EXPORT lean_object* l_Vector_ofFnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__26____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__22____x40_Init_Data_Vector_OfFn___hyg_2743_;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__25____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__24____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__7____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__19____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__18____x40_Init_Data_Vector_OfFn___hyg_2743_;
LEAN_EXPORT lean_object* l_Vector_ofFnM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l___auto___closed__13____x40_Init_Data_Vector_OfFn___hyg_2743_;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___auto___closed__20____x40_Init_Data_Vector_OfFn___hyg_2743_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_;
static lean_object* l___auto___closed__8____x40_Init_Data_Vector_OfFn___hyg_2743_;
LEAN_EXPORT lean_object* l_Vector_ofFnM_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l_Vector_ofFnM_go___redArg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Vector_ofFnM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_3);
x_12 = lean_apply_1(x_3, x_4);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Vector_ofFnM_go___redArg(x_3, x_4, x_5, x_6, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Vector_ofFnM_go___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_1);
x_6 = l_Vector_ofFnM_go___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Vector_ofFnM___redArg(x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__3____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_4 = l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__6____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__6____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_4 = l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__8____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("omega", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto___closed__11____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_4 = l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__12____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__13____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__12____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__14____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__15____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__14____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_4 = l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__16____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__17____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__18____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__17____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__15____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__19____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__18____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__13____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__20____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__19____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__11____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__21____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__20____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__22____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__21____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__23____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__22____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__24____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__23____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__7____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__25____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__24____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__26____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__25____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_2 = l___auto___closed__4____x40_Init_Data_Vector_OfFn___hyg_2743_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Vector_OfFn___hyg_2743_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__26____x40_Init_Data_Vector_OfFn___hyg_2743_;
return x_1;
}
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_OfFn(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__0____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__1____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__2____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__3____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__3____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__3____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__4____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__4____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__4____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__5____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__6____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__6____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__6____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__7____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__7____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__7____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__8____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__8____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__8____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__9____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__10____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__11____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__11____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__11____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__12____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__12____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__12____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__13____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__13____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__13____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__14____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__14____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__14____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__15____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__15____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__15____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__16____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__16____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__16____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__17____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__17____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__17____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__18____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__18____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__18____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__19____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__19____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__19____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__20____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__20____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__20____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__21____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__21____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__21____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__22____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__22____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__22____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__23____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__23____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__23____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__24____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__24____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__24____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__25____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__25____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__25____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto___closed__26____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto___closed__26____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto___closed__26____x40_Init_Data_Vector_OfFn___hyg_2743_);
l___auto____x40_Init_Data_Vector_OfFn___hyg_2743_ = _init_l___auto____x40_Init_Data_Vector_OfFn___hyg_2743_();
lean_mark_persistent(l___auto____x40_Init_Data_Vector_OfFn___hyg_2743_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
