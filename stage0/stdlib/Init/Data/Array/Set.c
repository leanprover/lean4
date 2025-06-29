// Lean compiler output
// Module: Init.Data.Array.Set
// Imports: Init.Tactics
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
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17_;
LEAN_EXPORT lean_object* l_Array_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__6____x40_Init_Data_Array_Set___hyg_17_;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Init_Data_Array_Set___hyg_17_;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__8____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__12____x40_Init_Data_Array_Set___hyg_17_;
lean_object* l_Array_empty(lean_object*);
static lean_object* l___auto___closed__19____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__17____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__16____x40_Init_Data_Array_Set___hyg_17_;
LEAN_EXPORT lean_object* l_Array_setIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__18____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__7____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__11____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__20____x40_Init_Data_Array_Set___hyg_17_;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__14____x40_Init_Data_Array_Set___hyg_17_;
LEAN_EXPORT lean_object* l_Array_setIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__4____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__9____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* l___auto___closed__10____x40_Init_Data_Array_Set___hyg_17_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__13____x40_Init_Data_Array_Set___hyg_17_;
LEAN_EXPORT lean_object* l_Array_set_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l___auto___closed__3____x40_Init_Data_Array_Set___hyg_17_;
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_;
static lean_object* _init_l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__3____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_;
x_3 = l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_;
x_4 = l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__6____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__6____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_;
x_3 = l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_;
x_4 = l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__8____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__10____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic", 21, 21);
return x_1;
}
}
static lean_object* _init_l___auto___closed__11____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__10____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__12____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get_elem_tactic", 15, 15);
return x_1;
}
}
static lean_object* _init_l___auto___closed__13____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__12____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__14____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__13____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__15____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__14____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__11____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__16____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__15____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__17____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__16____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__9____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__18____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__17____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__19____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__18____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__7____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__20____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__19____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__21____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__20____x40_Init_Data_Array_Set___hyg_17_;
x_2 = l___auto___closed__4____x40_Init_Data_Array_Set___hyg_17_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__21____x40_Init_Data_Array_Set___hyg_17_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_array_fset(x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fset(x_1, x_2, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fset(x_2, x_3, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_setIfInBounds___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_setIfInBounds(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_set(x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Set(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__0____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__1____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__2____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__3____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__3____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__3____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__4____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__4____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__4____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__5____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__6____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__6____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__6____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__7____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__7____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__7____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__8____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__8____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__8____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__9____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__9____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__9____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__10____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__10____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__10____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__11____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__11____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__11____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__12____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__12____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__12____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__13____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__13____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__13____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__14____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__14____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__14____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__15____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__15____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__15____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__16____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__16____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__16____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__17____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__17____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__17____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__18____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__18____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__18____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__19____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__19____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__19____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__20____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__20____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__20____x40_Init_Data_Array_Set___hyg_17_);
l___auto___closed__21____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto___closed__21____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto___closed__21____x40_Init_Data_Array_Set___hyg_17_);
l___auto____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
