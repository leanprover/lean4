// Lean compiler output
// Module: Init.Data.Array.Attach
// Imports: Init.Data.Array.Mem Init.Data.Array.Lemmas Init.Data.Array.Count Init.Data.List.Attach
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
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__0;
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Array_pmap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_attach(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__7;
LEAN_EXPORT lean_object* l_Array_attach___redArg___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__6;
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__5;
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__2;
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Array_pmap_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_unattach(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__3;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg(size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Array_pmap_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_6, lean_box(0));
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_10, lean_box(0));
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Array_pmap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapTR_loop___at___Array_pmap_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_pmap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_to_list(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at___Array_pmap_spec__0___redArg(x_1, x_3, x_4);
x_6 = lean_array_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_pmap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_pmap___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_attach___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_attach(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_attach___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_attach___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_attach___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_attach(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__1;
x_2 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__5;
x_2 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__4;
x_3 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__3;
x_4 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__2;
x_5 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__6;
x_2 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9;
x_5 = lean_array_size(x_2);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___redArg(x_4, x_3, x_5, x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_pmapImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9;
x_9 = lean_array_size(x_5);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___redArg(x_8, x_7, x_9, x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_unattach___redArg(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_unattach(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_unattach___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___redArg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_unattach_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Array_unattach_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Count(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Mem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Count(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__0 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__0);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__1 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__1);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__2 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__2);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__3 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__3);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__4 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__4);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__5 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__5);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__6 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__6();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__6);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__7 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__7();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__7);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__8 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__8();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__8);
l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9 = _init_l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9();
lean_mark_persistent(l___private_Init_Data_Array_Attach_0__Array_pmapImpl___redArg___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
