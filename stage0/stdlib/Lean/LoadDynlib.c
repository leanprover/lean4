// Lean compiler output
// Module: Lean.LoadDynlib
// Imports: Init.System.IO
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
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object*, lean_object*);
lean_object* l_String_stripSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_stripPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object*, lean_object*);
lean_object* lean_dynlib_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object*, lean_object*);
lean_object* lean_dynlib_symbol_run_as_init(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__5;
static lean_object* l_Lean_loadPlugin___closed__3;
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__2;
static lean_object* l_Lean_loadPlugin___closed__4;
static lean_object* l_Lean_loadPlugin___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__0;
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*, lean_object*);
lean_object* lean_dynlib_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object*);
static lean_object* _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_load(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_get(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_load(x_1, x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_runtime_mark_persistent(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error, plugin has invalid file name '", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_shared", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialize_", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error loading plugin, initializer not found '", 45, 45);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_load_plugin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_7 = l_System_FilePath_fileStem(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_loadPlugin___closed__0;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_Lean_loadPlugin___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_mk_io_user_error(x_11);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_3);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec_ref(x_7);
x_14 = lean_dynlib_load(x_5, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_loadPlugin___closed__2;
x_19 = l_String_stripPrefix(x_13, x_18);
x_20 = l_Lean_loadPlugin___closed__3;
x_21 = l_String_stripSuffix(x_19, x_20);
x_22 = l_Lean_loadPlugin___closed__4;
x_23 = lean_string_append(x_22, x_21);
lean_dec_ref(x_21);
x_24 = lean_dynlib_get(x_16, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_25 = l_Lean_loadPlugin___closed__5;
x_26 = lean_string_append(x_25, x_23);
lean_dec_ref(x_23);
x_27 = l_Lean_loadPlugin___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_mk_io_user_error(x_28);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_23);
lean_free_object(x_14);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec_ref(x_24);
lean_inc(x_16);
x_31 = lean_runtime_mark_persistent(x_16, x_17);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_dynlib_symbol_run_as_init(x_16, x_30, x_32);
lean_dec(x_30);
lean_dec(x_16);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = l_Lean_loadPlugin___closed__2;
x_37 = l_String_stripPrefix(x_13, x_36);
x_38 = l_Lean_loadPlugin___closed__3;
x_39 = l_String_stripSuffix(x_37, x_38);
x_40 = l_Lean_loadPlugin___closed__4;
x_41 = lean_string_append(x_40, x_39);
lean_dec_ref(x_39);
x_42 = lean_dynlib_get(x_34, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
x_43 = l_Lean_loadPlugin___closed__5;
x_44 = lean_string_append(x_43, x_41);
lean_dec_ref(x_41);
x_45 = l_Lean_loadPlugin___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_mk_io_user_error(x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec_ref(x_42);
lean_inc(x_34);
x_50 = lean_runtime_mark_persistent(x_34, x_35);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_dynlib_symbol_run_as_init(x_34, x_49, x_51);
lean_dec(x_49);
lean_dec(x_34);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
lean_inc(x_57);
x_59 = l_System_FilePath_fileStem(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = l_Lean_loadPlugin___closed__0;
x_61 = lean_string_append(x_60, x_57);
lean_dec(x_57);
x_62 = l_Lean_loadPlugin___closed__1;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_mk_io_user_error(x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
lean_dec_ref(x_59);
x_67 = lean_dynlib_load(x_57, x_58);
lean_dec(x_57);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = l_Lean_loadPlugin___closed__2;
x_72 = l_String_stripPrefix(x_66, x_71);
x_73 = l_Lean_loadPlugin___closed__3;
x_74 = l_String_stripSuffix(x_72, x_73);
x_75 = l_Lean_loadPlugin___closed__4;
x_76 = lean_string_append(x_75, x_74);
lean_dec_ref(x_74);
x_77 = lean_dynlib_get(x_68, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_78 = l_Lean_loadPlugin___closed__5;
x_79 = lean_string_append(x_78, x_76);
lean_dec_ref(x_76);
x_80 = l_Lean_loadPlugin___closed__1;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_mk_io_user_error(x_81);
if (lean_is_scalar(x_70)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_70;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_69);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_76);
lean_dec(x_70);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
lean_dec_ref(x_77);
lean_inc(x_68);
x_85 = lean_runtime_mark_persistent(x_68, x_69);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_dynlib_symbol_run_as_init(x_68, x_84, x_86);
lean_dec(x_84);
lean_dec(x_68);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_66);
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_90 = x_67;
} else {
 lean_dec_ref(x_67);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_3);
if (x_92 == 0)
{
return x_3;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_3, 0);
x_94 = lean_ctor_get(x_3, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_3);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_LoadDynlib_0__Lean_DynlibImpl = _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl();
l_Lean_loadPlugin___closed__0 = _init_l_Lean_loadPlugin___closed__0();
lean_mark_persistent(l_Lean_loadPlugin___closed__0);
l_Lean_loadPlugin___closed__1 = _init_l_Lean_loadPlugin___closed__1();
lean_mark_persistent(l_Lean_loadPlugin___closed__1);
l_Lean_loadPlugin___closed__2 = _init_l_Lean_loadPlugin___closed__2();
lean_mark_persistent(l_Lean_loadPlugin___closed__2);
l_Lean_loadPlugin___closed__3 = _init_l_Lean_loadPlugin___closed__3();
lean_mark_persistent(l_Lean_loadPlugin___closed__3);
l_Lean_loadPlugin___closed__4 = _init_l_Lean_loadPlugin___closed__4();
lean_mark_persistent(l_Lean_loadPlugin___closed__4);
l_Lean_loadPlugin___closed__5 = _init_l_Lean_loadPlugin___closed__5();
lean_mark_persistent(l_Lean_loadPlugin___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
