// Lean compiler output
// Module: Init.Data.Queue
// Imports: public import Init.Data.List.Control
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
static const lean_ctor_object l_Std_Queue_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Queue_empty___closed__0 = (const lean_object*)&l_Std_Queue_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object*);
static lean_once_cell_t l_Std_Queue_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Queue_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Queue_empty___closed__0));
return x_2;
}
}
static lean_object* _init_l_Std_Queue_instEmptyCollection___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Std_Queue_instEmptyCollection___closed__0, &l_Std_Queue_instEmptyCollection___closed__0_once, _init_l_Std_Queue_instEmptyCollection___closed__0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Std_Queue_instEmptyCollection___closed__0, &l_Std_Queue_instEmptyCollection___closed__0_once, _init_l_Std_Queue_instEmptyCollection___closed__0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_List_isEmpty___redArg(x_3);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_List_isEmpty___redArg(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Queue_isEmpty___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Queue_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Queue_isEmpty(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_4);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Queue_enqueue___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_appendTR___redArg(x_1, x_3);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_4);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Queue_enqueueAll___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 0);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_4 = x_1;
x_5 = x_22;
goto block_21;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_6; 
x_6 = l_List_reverse___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_del_object(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_20; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
x_10 = x_6;
x_11 = x_20;
goto block_19;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_12; 
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_2);
x_12 = x_4;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_9);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; 
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_12);
x_13 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_12);
x_13 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_41; 
x_24 = lean_ctor_get(x_1, 0);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_1, 1);
lean_dec(x_42);
x_25 = x_1;
x_26 = x_41;
goto block_40;
}
else
{
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_39; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
x_29 = x_2;
x_30 = x_39;
goto block_38;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_31; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_28);
x_31 = x_25;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_28);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; 
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 1, x_31);
x_32 = x_29;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_31);
x_32 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Queue_dequeue_x3f___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_array_mk(x_3);
x_5 = lean_array_mk(x_2);
x_6 = l_Array_reverse___redArg(x_5);
x_7 = l_Array_append___redArg(x_4, x_6);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Queue_toArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_isEmpty___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = l_List_reverse___redArg(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_box(0);
x_9 = l_List_filterAuxM___redArg(x_2, x_3, x_4, x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_5);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__2), 6, 5);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_6);
lean_closure_set(x_9, 4, x_5);
x_10 = lean_box(0);
x_11 = l_List_filterAuxM___redArg(x_1, x_2, x_7, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_8);
lean_inc(x_5);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Queue_filterM___redArg(x_2, x_4, x_5);
return x_6;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Control(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Queue(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Queue(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Queue(builtin);
}
#ifdef __cplusplus
}
#endif
