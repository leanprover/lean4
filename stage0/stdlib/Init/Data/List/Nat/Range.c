// Lean compiler output
// Module: Init.Data.List.Nat.Range
// Imports: Init.Data.List.Nat.TakeDrop Init.Data.List.Range Init.Data.List.Pairwise Init.Data.List.Find Init.Data.List.Erase
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
static lean_object* l___auto___closed__18____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__22____x40_Init_Data_List_Nat_Range___hyg_141_;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__21____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__28____x40_Init_Data_List_Nat_Range___hyg_141_;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto___closed__19____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__14____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__4____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__15____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__7____x40_Init_Data_List_Nat_Range___hyg_141_;
lean_object* l_Array_empty(lean_object*);
static lean_object* l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__23____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__12____x40_Init_Data_List_Nat_Range___hyg_141_;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_List_Nat_Range___hyg_201_;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_List_Nat_Range___hyg_610_;
static lean_object* l___auto___closed__29____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__13____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__3____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__27____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__24____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__25____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__17____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__11____x40_Init_Data_List_Nat_Range___hyg_141_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l___auto___closed__20____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__6____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__8____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* l___auto___closed__26____x40_Init_Data_List_Nat_Range___hyg_141_;
static lean_object* _init_l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__3____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_;
x_4 = l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__6____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__6____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_;
x_4 = l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__8____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__11____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_;
x_4 = l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__12____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__13____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__12____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__14____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__15____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__14____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_;
x_4 = l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__17____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__18____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__17____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__15____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__19____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__18____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__13____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__20____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__19____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__21____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__20____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__22____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__21____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__23____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__22____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__24____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__23____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__11____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__25____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__24____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__26____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__25____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__27____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__26____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__28____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__27____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__7____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__29____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__28____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__29____x40_Init_Data_List_Nat_Range___hyg_141_;
x_2 = l___auto___closed__4____x40_Init_Data_List_Nat_Range___hyg_141_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_;
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_201_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_;
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_610_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_;
return x_1;
}
}
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Nat_TakeDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__0____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__1____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__2____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__3____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__3____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__3____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__4____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__4____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__4____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__5____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__6____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__6____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__6____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__7____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__7____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__7____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__8____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__8____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__8____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__9____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__10____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__11____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__11____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__11____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__12____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__12____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__12____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__13____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__13____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__13____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__14____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__14____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__14____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__15____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__15____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__15____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__16____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__17____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__17____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__17____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__18____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__18____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__18____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__19____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__19____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__19____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__20____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__20____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__20____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__21____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__21____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__21____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__22____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__22____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__22____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__23____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__23____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__23____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__24____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__24____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__24____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__25____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__25____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__25____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__26____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__26____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__26____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__27____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__27____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__27____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__28____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__28____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__28____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__29____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__29____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__29____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto___closed__30____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto____x40_Init_Data_List_Nat_Range___hyg_201_ = _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_201_();
lean_mark_persistent(l___auto____x40_Init_Data_List_Nat_Range___hyg_201_);
l___auto____x40_Init_Data_List_Nat_Range___hyg_610_ = _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_610_();
lean_mark_persistent(l___auto____x40_Init_Data_List_Nat_Range___hyg_610_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
