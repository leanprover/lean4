// Lean compiler output
// Module: Lean.LoadDynlib
// Imports: public import Init.System.IO import Init.Data.String.TakeDrop
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
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object*);
lean_object* lean_dynlib_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object*);
lean_object* lean_dynlib_symbol_run_as_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__5;
static lean_object* l_Lean_loadPlugin___closed__3;
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*);
lean_object* lean_io_realpath(lean_object*);
static lean_object* l_Lean_loadPlugin___closed__2;
static lean_object* l_Lean_loadPlugin___closed__4;
static lean_object* l_Lean_loadPlugin___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__0;
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
lean_object* lean_dynlib_load(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object*, lean_object*);
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
x_3 = lean_dynlib_load(x_1);
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
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_load(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_runtime_mark_persistent(x_5);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_runtime_mark_persistent(x_8);
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_load_dynlib(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(x_1, x_2);
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
LEAN_EXPORT lean_object* lean_load_plugin(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_System_FilePath_fileStem(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_loadPlugin___closed__0;
x_8 = lean_string_append(x_7, x_5);
lean_dec(x_5);
x_9 = l_Lean_loadPlugin___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_mk_io_user_error(x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_3);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_dynlib_load(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_loadPlugin___closed__2;
x_17 = l_String_stripPrefix(x_12, x_16);
x_18 = l_Lean_loadPlugin___closed__3;
x_19 = l_String_stripSuffix(x_17, x_18);
x_20 = l_Lean_loadPlugin___closed__4;
x_21 = lean_string_append(x_20, x_19);
lean_dec_ref(x_19);
x_22 = lean_dynlib_get(x_15, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_23 = l_Lean_loadPlugin___closed__5;
x_24 = lean_string_append(x_23, x_21);
lean_dec_ref(x_21);
x_25 = l_Lean_loadPlugin___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_mk_io_user_error(x_26);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_21);
lean_free_object(x_13);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec_ref(x_22);
lean_inc(x_15);
x_29 = lean_runtime_mark_persistent(x_15);
lean_dec(x_29);
x_30 = lean_dynlib_symbol_run_as_init(x_15, x_28);
lean_dec(x_28);
lean_dec(x_15);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = l_Lean_loadPlugin___closed__2;
x_33 = l_String_stripPrefix(x_12, x_32);
x_34 = l_Lean_loadPlugin___closed__3;
x_35 = l_String_stripSuffix(x_33, x_34);
x_36 = l_Lean_loadPlugin___closed__4;
x_37 = lean_string_append(x_36, x_35);
lean_dec_ref(x_35);
x_38 = lean_dynlib_get(x_31, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_31);
x_39 = l_Lean_loadPlugin___closed__5;
x_40 = lean_string_append(x_39, x_37);
lean_dec_ref(x_37);
x_41 = l_Lean_loadPlugin___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_mk_io_user_error(x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
lean_inc(x_31);
x_46 = lean_runtime_mark_persistent(x_31);
lean_dec(x_46);
x_47 = lean_dynlib_symbol_run_as_init(x_31, x_45);
lean_dec(x_45);
lean_dec(x_31);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_12);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_13, 0);
lean_inc(x_49);
lean_dec(x_13);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
lean_dec(x_3);
lean_inc(x_51);
x_52 = l_System_FilePath_fileStem(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = l_Lean_loadPlugin___closed__0;
x_54 = lean_string_append(x_53, x_51);
lean_dec(x_51);
x_55 = l_Lean_loadPlugin___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_mk_io_user_error(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec_ref(x_52);
x_60 = lean_dynlib_load(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = l_Lean_loadPlugin___closed__2;
x_64 = l_String_stripPrefix(x_59, x_63);
x_65 = l_Lean_loadPlugin___closed__3;
x_66 = l_String_stripSuffix(x_64, x_65);
x_67 = l_Lean_loadPlugin___closed__4;
x_68 = lean_string_append(x_67, x_66);
lean_dec_ref(x_66);
x_69 = lean_dynlib_get(x_61, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
x_70 = l_Lean_loadPlugin___closed__5;
x_71 = lean_string_append(x_70, x_68);
lean_dec_ref(x_68);
x_72 = l_Lean_loadPlugin___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_mk_io_user_error(x_73);
if (lean_is_scalar(x_62)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_62;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_68);
lean_dec(x_62);
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec_ref(x_69);
lean_inc(x_61);
x_77 = lean_runtime_mark_persistent(x_61);
lean_dec(x_77);
x_78 = lean_dynlib_symbol_run_as_init(x_61, x_76);
lean_dec(x_76);
lean_dec(x_61);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_59);
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_80 = x_60;
} else {
 lean_dec_ref(x_60);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
return x_3;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
lean_dec(x_3);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_load_plugin(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
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
