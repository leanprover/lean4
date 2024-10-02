// Lean compiler output
// Module: Lake.Load.Lean
// Imports: Init Lake.Load.Lean.Elab Lake.Load.Lean.Eval
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
static lean_object* l_Lake_loadLeanConfig___closed__2;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_empty___rarg(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_loadFromEnv(lean_object*, lean_object*);
lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__1;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 18);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_loadLeanConfig___closed__2;
x_2 = l_Lake_RBArray_empty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lake_importConfigFile(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_110; lean_object* x_111; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_9);
x_110 = l_Lake_PackageConfig_loadFromEnv(x_9, x_11);
x_111 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_110, x_6);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_ctor_set(x_5, 0, x_112);
x_12 = x_5;
x_13 = x_113;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_io_error_to_string(x_114);
x_117 = 3;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
x_119 = lean_array_get_size(x_10);
x_120 = lean_array_push(x_10, x_118);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_120);
lean_ctor_set(x_5, 0, x_119);
x_12 = x_5;
x_13 = x_115;
goto block_109;
}
block_109:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 6);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_14, 17);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 19);
lean_inc(x_24);
x_25 = l_Lake_defaultManifestFile;
x_26 = l_Lake_loadLeanConfig___closed__1;
x_27 = l_Lake_loadLeanConfig___closed__3;
x_28 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_14);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_21);
lean_ctor_set(x_28, 6, x_26);
lean_ctor_set(x_28, 7, x_26);
lean_ctor_set(x_28, 8, x_27);
lean_ctor_set(x_28, 9, x_27);
lean_ctor_set(x_28, 10, x_22);
lean_ctor_set(x_28, 11, x_22);
lean_ctor_set(x_28, 12, x_26);
lean_ctor_set(x_28, 13, x_22);
lean_ctor_set(x_28, 14, x_26);
lean_ctor_set(x_28, 15, x_26);
lean_ctor_set(x_28, 16, x_23);
lean_ctor_set(x_28, 17, x_24);
lean_inc(x_9);
x_29 = l_Lake_Package_loadFromEnv(x_28, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_30, 0, x_35);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_9);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_29, 0, x_39);
return x_29;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_43 = x_30;
} else {
 lean_dec_ref(x_30);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_9);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_29, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_29, 0, x_52);
return x_29;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_dec(x_29);
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_56 = x_30;
} else {
 lean_dec_ref(x_30);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_9);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
return x_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_29, 0);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_29);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_14, 17);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 19);
lean_inc(x_64);
x_65 = lean_ctor_get(x_20, 0);
lean_inc(x_65);
lean_dec(x_20);
x_66 = l_Lake_loadLeanConfig___closed__1;
x_67 = l_Lake_loadLeanConfig___closed__3;
x_68 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_17);
lean_ctor_set(x_68, 2, x_14);
lean_ctor_set(x_68, 3, x_19);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_21);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_66);
lean_ctor_set(x_68, 8, x_67);
lean_ctor_set(x_68, 9, x_67);
lean_ctor_set(x_68, 10, x_22);
lean_ctor_set(x_68, 11, x_22);
lean_ctor_set(x_68, 12, x_66);
lean_ctor_set(x_68, 13, x_22);
lean_ctor_set(x_68, 14, x_66);
lean_ctor_set(x_68, 15, x_66);
lean_ctor_set(x_68, 16, x_63);
lean_ctor_set(x_68, 17, x_64);
lean_inc(x_9);
x_69 = l_Lake_Package_loadFromEnv(x_68, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
lean_ctor_set(x_70, 0, x_75);
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_9);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_69, 0, x_79);
return x_69;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_69, 1);
lean_inc(x_80);
lean_dec(x_69);
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_83 = x_70;
} else {
 lean_dec_ref(x_70);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_9);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_9);
x_87 = !lean_is_exclusive(x_69);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_69, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_70);
if (x_89 == 0)
{
return x_69;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_70, 0);
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_70);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_69, 0, x_92);
return x_69;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_69, 1);
lean_inc(x_93);
lean_dec(x_69);
x_94 = lean_ctor_get(x_70, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_96 = x_70;
} else {
 lean_dec_ref(x_70);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_9);
x_99 = !lean_is_exclusive(x_69);
if (x_99 == 0)
{
return x_69;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_69, 0);
x_101 = lean_ctor_get(x_69, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_69);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_12);
if (x_103 == 0)
{
lean_object* x_104; 
if (lean_is_scalar(x_7)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_7;
}
lean_ctor_set(x_104, 0, x_12);
lean_ctor_set(x_104, 1, x_13);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_12, 0);
x_106 = lean_ctor_get(x_12, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_12);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_7)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_7;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_13);
return x_108;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_195; lean_object* x_196; 
x_121 = lean_ctor_get(x_5, 0);
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_5);
x_123 = lean_ctor_get(x_1, 5);
lean_inc(x_123);
lean_inc(x_121);
x_195 = l_Lake_PackageConfig_loadFromEnv(x_121, x_123);
x_196 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_195, x_6);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_122);
x_124 = x_199;
x_125 = x_198;
goto block_194;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
lean_dec(x_196);
x_202 = lean_io_error_to_string(x_200);
x_203 = 3;
x_204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_203);
x_205 = lean_array_get_size(x_122);
x_206 = lean_array_push(x_122, x_204);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_124 = x_207;
x_125 = x_201;
goto block_194;
}
block_194:
{
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_7);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_1, 2);
lean_inc(x_129);
x_130 = l_System_FilePath_join(x_128, x_129);
x_131 = lean_ctor_get(x_1, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_126, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 6);
lean_inc(x_133);
lean_dec(x_1);
x_134 = lean_box(0);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_126, 17);
lean_inc(x_135);
x_136 = lean_ctor_get(x_126, 19);
lean_inc(x_136);
x_137 = l_Lake_defaultManifestFile;
x_138 = l_Lake_loadLeanConfig___closed__1;
x_139 = l_Lake_loadLeanConfig___closed__3;
x_140 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_140, 0, x_130);
lean_ctor_set(x_140, 1, x_129);
lean_ctor_set(x_140, 2, x_126);
lean_ctor_set(x_140, 3, x_131);
lean_ctor_set(x_140, 4, x_137);
lean_ctor_set(x_140, 5, x_133);
lean_ctor_set(x_140, 6, x_138);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set(x_140, 8, x_139);
lean_ctor_set(x_140, 9, x_139);
lean_ctor_set(x_140, 10, x_134);
lean_ctor_set(x_140, 11, x_134);
lean_ctor_set(x_140, 12, x_138);
lean_ctor_set(x_140, 13, x_134);
lean_ctor_set(x_140, 14, x_138);
lean_ctor_set(x_140, 15, x_138);
lean_ctor_set(x_140, 16, x_135);
lean_ctor_set(x_140, 17, x_136);
lean_inc(x_121);
x_141 = l_Lake_Package_loadFromEnv(x_140, x_121, x_123, x_127, x_125);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_121);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
if (lean_is_scalar(x_144)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_144;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_143);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_121);
x_151 = lean_ctor_get(x_141, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_152 = x_141;
} else {
 lean_dec_ref(x_141);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_142, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_155 = x_142;
} else {
 lean_dec_ref(x_142);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_151);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_121);
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_141, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_160 = x_141;
} else {
 lean_dec_ref(x_141);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_126, 17);
lean_inc(x_162);
x_163 = lean_ctor_get(x_126, 19);
lean_inc(x_163);
x_164 = lean_ctor_get(x_132, 0);
lean_inc(x_164);
lean_dec(x_132);
x_165 = l_Lake_loadLeanConfig___closed__1;
x_166 = l_Lake_loadLeanConfig___closed__3;
x_167 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_167, 0, x_130);
lean_ctor_set(x_167, 1, x_129);
lean_ctor_set(x_167, 2, x_126);
lean_ctor_set(x_167, 3, x_131);
lean_ctor_set(x_167, 4, x_164);
lean_ctor_set(x_167, 5, x_133);
lean_ctor_set(x_167, 6, x_165);
lean_ctor_set(x_167, 7, x_165);
lean_ctor_set(x_167, 8, x_166);
lean_ctor_set(x_167, 9, x_166);
lean_ctor_set(x_167, 10, x_134);
lean_ctor_set(x_167, 11, x_134);
lean_ctor_set(x_167, 12, x_165);
lean_ctor_set(x_167, 13, x_134);
lean_ctor_set(x_167, 14, x_165);
lean_ctor_set(x_167, 15, x_165);
lean_ctor_set(x_167, 16, x_162);
lean_ctor_set(x_167, 17, x_163);
lean_inc(x_121);
x_168 = l_Lake_Package_loadFromEnv(x_167, x_121, x_123, x_127, x_125);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_174 = x_169;
} else {
 lean_dec_ref(x_169);
 x_174 = lean_box(0);
}
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_121);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_171;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_170);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_121);
x_178 = lean_ctor_get(x_168, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_179 = x_168;
} else {
 lean_dec_ref(x_168);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_169, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_169, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_182 = x_169;
} else {
 lean_dec_ref(x_169);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_121);
x_185 = lean_ctor_get(x_168, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_168, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_187 = x_168;
} else {
 lean_dec_ref(x_168);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_1);
x_189 = lean_ctor_get(x_124, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_124, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_191 = x_124;
} else {
 lean_dec_ref(x_124);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
if (lean_is_scalar(x_7)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_7;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_125);
return x_193;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_4);
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_4, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_5);
if (x_210 == 0)
{
return x_4;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_5, 0);
x_212 = lean_ctor_get(x_5, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_5);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_4, 0, x_213);
return x_4;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_4, 1);
lean_inc(x_214);
lean_dec(x_4);
x_215 = lean_ctor_get(x_5, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_5, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_217 = x_5;
} else {
 lean_dec_ref(x_5);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_214);
return x_219;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_loadLeanConfig___closed__1 = _init_l_Lake_loadLeanConfig___closed__1();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__1);
l_Lake_loadLeanConfig___closed__2 = _init_l_Lake_loadLeanConfig___closed__2();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__2);
l_Lake_loadLeanConfig___closed__3 = _init_l_Lake_loadLeanConfig___closed__3();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
