// Lean compiler output
// Module: Lean.Server.ServerBin
// Imports: Init Init.System.IO Lean.Server
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
lean_object* lean_get_stdin(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* _lean_main(lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
lean_object* l_main___boxed__const__1;
lean_object* l_IO_getStdin___at_main___spec__1(lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Test_runWithInputFile___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_initAndRunServer(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdin___at_main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin(x_1);
return x_2;
}
}
static lean_object* _init_l_main___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _lean_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_get_stdin(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_init_search_path(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Server_initAndRunServer(x_4, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_main___boxed__const__1;
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_main___boxed__const__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_io_error_to_string(x_22);
x_25 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Test_runWithInputFile___spec__1(x_10, x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_main___boxed__const__1;
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_main___boxed__const__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
return x_6;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_6, 0);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
return x_3;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Lean_Server(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_ServerBin(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  lean_object* in; lean_object* res;
lean_initialize();
res = initialize_Lean_Server_ServerBin(lean_io_mk_world());
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
in = lean_box(0);
int i = argc;
while (i > 1) {
 lean_object* n;
 i--;
 n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
 in = n;
}
res = _lean_main(in, lean_io_mk_world());
}
if (lean_io_result_is_ok(res)) {
  int ret = lean_unbox(lean_io_result_get_value(res));
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
