// Lean compiler output
// Module: Lean.Shell
// Imports: Lean.Elab.Frontend Lean.Compiler.IR.EmitC
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_run_main(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3;
lean_object* lean_init_llvm(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
lean_object* lean_display_cumulative_profiling_times(lean_object*);
uint8_t lean_internal_has_address_sanitizer(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_ir_emit_c(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_run_main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_init_llvm(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_emit_llvm(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_display_cumulative_profiling_times(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_has_address_sanitizer(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_address_sanitizer(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_13; 
x_4 = lean_display_cumulative_profiling_times(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_13 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
if (x_13 == 0)
{
lean_dec(x_6);
if (lean_obj_tag(x_1) == 0)
{
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
x_15 = lean_io_exit(x_14, x_5);
return x_15;
}
else
{
goto block_12;
}
}
else
{
goto block_12;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
goto block_9;
}
else
{
if (x_13 == 0)
{
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(0, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
block_12:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_io_exit(x_10, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_8 = lean_io_prim_handle_write(x_2, x_7, x_6);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LLVM code generation", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("C code generation", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create '", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint32_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, uint8_t x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_97; 
x_97 = lean_box(0);
x_42 = x_97;
x_43 = x_16;
x_44 = x_5;
goto block_96;
}
else
{
uint8_t x_98; 
lean_dec(x_5);
x_98 = !lean_is_exclusive(x_14);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_14, 0);
x_100 = l_Lean_ModuleSetup_load(x_99, x_16);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_ctor_set(x_14, 0, x_101);
x_42 = x_14;
x_43 = x_102;
x_44 = x_103;
goto block_96;
}
else
{
uint8_t x_104; 
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_100, 0);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_100);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_14, 0);
lean_inc(x_108);
lean_dec(x_14);
x_109 = l_Lean_ModuleSetup_load(x_108, x_16);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_42 = x_113;
x_43 = x_111;
x_44 = x_112;
goto block_96;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
block_41:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_17, x_21, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_init_llvm(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Shell_0__Lean_shellMain___closed__0;
x_27 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(x_27, 0, x_18);
lean_closure_set(x_27, 1, x_19);
lean_closure_set(x_27, 2, x_23);
x_28 = lean_box(0);
x_29 = l_Lean_profileitIOUnsafe___redArg(x_26, x_3, x_27, x_28, x_25);
lean_dec(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_apply_2(x_17, x_30, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
block_96:
{
lean_object* x_45; lean_object* x_46; 
x_45 = l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_inc(x_44);
lean_inc(x_3);
x_46 = l_Lean_Elab_runFrontend(x_2, x_3, x_4, x_44, x_6, x_7, x_8, x_11, x_12, x_45, x_13, x_42, x_43);
lean_dec(x_12);
lean_dec(x_8);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_47);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 1);
lean_closure_set(x_49, 0, x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_47, x_50, x_48);
return x_51;
}
else
{
if (x_15 == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_17 = x_49;
x_18 = x_52;
x_19 = x_44;
x_20 = x_48;
goto block_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_9, 0);
lean_inc(x_54);
lean_dec(x_9);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
x_57 = lean_io_prim_handle_mk(x_54, x_56, x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
lean_inc(x_44);
lean_inc(x_53);
x_61 = lean_ir_emit_c(x_53, x_44);
x_62 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 3, 2);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_58);
x_63 = lean_box(0);
x_64 = l_Lean_profileitIOUnsafe___redArg(x_60, x_3, x_62, x_63, x_59);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_17 = x_49;
x_18 = x_53;
x_19 = x_44;
x_20 = x_65;
goto block_41;
}
else
{
uint8_t x_66; 
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_3);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_dec(x_57);
x_71 = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
x_72 = lean_string_append(x_71, x_54);
lean_dec(x_54);
x_73 = l___private_Lean_Shell_0__Lean_shellMain___closed__4;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_74, x_70);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
x_78 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
return x_75;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
x_86 = lean_ctor_get(x_47, 0);
lean_inc(x_86);
lean_dec(x_47);
x_87 = lean_run_main(x_86, x_3, x_1, x_48);
lean_dec(x_1);
lean_dec(x_3);
lean_dec(x_86);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_46);
if (x_92 == 0)
{
return x_46;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_46, 0);
x_94 = lean_ctor_get(x_46, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_46);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint32_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_unbox_uint32(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
x_19 = lean_unbox(x_13);
lean_dec(x_13);
x_20 = lean_unbox(x_15);
lean_dec(x_15);
x_21 = lean_shell_main(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_18, x_12, x_19, x_14, x_20, x_16);
return x_21;
}
}
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Shell(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Frontend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0();
l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1);
l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2);
l___private_Lean_Shell_0__Lean_shellMain___closed__0 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__0);
l___private_Lean_Shell_0__Lean_shellMain___closed__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__1);
l___private_Lean_Shell_0__Lean_shellMain___closed__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__2);
l___private_Lean_Shell_0__Lean_shellMain___closed__3 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__3);
l___private_Lean_Shell_0__Lean_shellMain___closed__4 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__4);
l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
