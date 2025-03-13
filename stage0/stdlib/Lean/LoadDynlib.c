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
LEAN_EXPORT lean_object* l_Lean_loadPlugin_unsafe__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadPlugin_unsafe__1(lean_object*, lean_object*);
lean_object* l_String_stripPrefix(lean_object*, lean_object*);
lean_object* lean_dynlib_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadDynlib_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
lean_object* lean_dynlib_symbol_run_as_init(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__5;
static lean_object* l_Lean_loadPlugin___closed__3;
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadPlugin_unsafe__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__2;
static lean_object* l_Lean_loadPlugin___closed__4;
static lean_object* l_Lean_loadPlugin___closed__1;
static lean_object* l_Lean_loadPlugin___closed__7;
static lean_object* l_Lean_loadPlugin___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_get(x_1, x_2);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_loadDynlib_unsafe__1(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_loadPlugin_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin_unsafe__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin_unsafe__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_loadPlugin_unsafe__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error, plugin has invalid file name '", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_shared", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialize_", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__7() {
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
x_8 = l_Lean_loadPlugin___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_Lean_loadPlugin___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
uint8_t x_13; 
lean_free_object(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_dynlib_load(x_5, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_loadPlugin___closed__3;
x_20 = l_String_stripPrefix(x_14, x_19);
x_21 = l_Lean_loadPlugin___closed__4;
x_22 = l_String_stripSuffix(x_20, x_21);
x_23 = l_Lean_loadPlugin___closed__5;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_loadPlugin___closed__6;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_dynlib_get(x_17, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
x_28 = l_Lean_loadPlugin___closed__7;
x_29 = lean_string_append(x_28, x_26);
lean_dec(x_26);
x_30 = l_Lean_loadPlugin___closed__2;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_31);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_free_object(x_15);
lean_free_object(x_7);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
lean_inc(x_17);
x_33 = lean_runtime_mark_persistent(x_17, x_18);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_dynlib_symbol_run_as_init(x_17, x_32, x_34);
lean_dec(x_32);
lean_dec(x_17);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = l_Lean_loadPlugin___closed__3;
x_39 = l_String_stripPrefix(x_14, x_38);
x_40 = l_Lean_loadPlugin___closed__4;
x_41 = l_String_stripSuffix(x_39, x_40);
x_42 = l_Lean_loadPlugin___closed__5;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lean_loadPlugin___closed__6;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_dynlib_get(x_36, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
x_47 = l_Lean_loadPlugin___closed__7;
x_48 = lean_string_append(x_47, x_45);
lean_dec(x_45);
x_49 = l_Lean_loadPlugin___closed__2;
x_50 = lean_string_append(x_48, x_49);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_50);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_37);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_45);
lean_free_object(x_7);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
lean_inc(x_36);
x_53 = lean_runtime_mark_persistent(x_36, x_37);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_dynlib_symbol_run_as_init(x_36, x_52, x_54);
lean_dec(x_52);
lean_dec(x_36);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_7);
lean_dec(x_14);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
return x_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
lean_dec(x_7);
x_61 = lean_dynlib_load(x_5, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = l_Lean_loadPlugin___closed__3;
x_66 = l_String_stripPrefix(x_60, x_65);
x_67 = l_Lean_loadPlugin___closed__4;
x_68 = l_String_stripSuffix(x_66, x_67);
x_69 = l_Lean_loadPlugin___closed__5;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lean_loadPlugin___closed__6;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_dynlib_get(x_62, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
x_74 = l_Lean_loadPlugin___closed__7;
x_75 = lean_string_append(x_74, x_72);
lean_dec(x_72);
x_76 = l_Lean_loadPlugin___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_64)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_64;
 lean_ctor_set_tag(x_79, 1);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_63);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_72);
lean_dec(x_64);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
lean_inc(x_62);
x_81 = lean_runtime_mark_persistent(x_62, x_63);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_dynlib_symbol_run_as_init(x_62, x_80, x_82);
lean_dec(x_80);
lean_dec(x_62);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_60);
x_84 = lean_ctor_get(x_61, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_61, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_86 = x_61;
} else {
 lean_dec_ref(x_61);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_3, 0);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_3);
lean_inc(x_88);
x_90 = l_System_FilePath_fileStem(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = l_Lean_loadPlugin___closed__1;
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
x_93 = l_Lean_loadPlugin___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_89);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
x_99 = lean_dynlib_load(x_88, x_89);
lean_dec(x_88);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = l_Lean_loadPlugin___closed__3;
x_104 = l_String_stripPrefix(x_97, x_103);
x_105 = l_Lean_loadPlugin___closed__4;
x_106 = l_String_stripSuffix(x_104, x_105);
x_107 = l_Lean_loadPlugin___closed__5;
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = l_Lean_loadPlugin___closed__6;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_dynlib_get(x_100, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_100);
x_112 = l_Lean_loadPlugin___closed__7;
x_113 = lean_string_append(x_112, x_110);
lean_dec(x_110);
x_114 = l_Lean_loadPlugin___closed__2;
x_115 = lean_string_append(x_113, x_114);
if (lean_is_scalar(x_98)) {
 x_116 = lean_alloc_ctor(18, 1, 0);
} else {
 x_116 = x_98;
 lean_ctor_set_tag(x_116, 18);
}
lean_ctor_set(x_116, 0, x_115);
if (lean_is_scalar(x_102)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_102;
 lean_ctor_set_tag(x_117, 1);
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_101);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_110);
lean_dec(x_102);
lean_dec(x_98);
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
lean_dec(x_111);
lean_inc(x_100);
x_119 = lean_runtime_mark_persistent(x_100, x_101);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_dynlib_symbol_run_as_init(x_100, x_118, x_120);
lean_dec(x_118);
lean_dec(x_100);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_98);
lean_dec(x_97);
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_99, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_124 = x_99;
} else {
 lean_dec_ref(x_99);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_3);
if (x_126 == 0)
{
return x_3;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_3, 0);
x_128 = lean_ctor_get(x_3, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_3);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
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
l_Lean_loadPlugin___closed__6 = _init_l_Lean_loadPlugin___closed__6();
lean_mark_persistent(l_Lean_loadPlugin___closed__6);
l_Lean_loadPlugin___closed__7 = _init_l_Lean_loadPlugin___closed__7();
lean_mark_persistent(l_Lean_loadPlugin___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
