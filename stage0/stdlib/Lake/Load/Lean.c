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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_111; lean_object* x_112; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_1, 6);
lean_inc(x_11);
lean_inc(x_9);
x_111 = l_Lake_PackageConfig_loadFromEnv(x_9, x_11);
x_112 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_111, x_6);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_ctor_set(x_5, 0, x_113);
x_12 = x_5;
x_13 = x_114;
goto block_110;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_io_error_to_string(x_115);
x_118 = 3;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_array_get_size(x_10);
x_121 = lean_array_push(x_10, x_119);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_121);
lean_ctor_set(x_5, 0, x_120);
x_12 = x_5;
x_13 = x_116;
goto block_110;
}
block_110:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 17);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 19);
lean_inc(x_25);
x_26 = l_Lake_defaultManifestFile;
x_27 = l_Lake_loadLeanConfig___closed__1;
x_28 = l_Lake_loadLeanConfig___closed__3;
x_29 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_14);
lean_ctor_set(x_29, 3, x_19);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_21);
lean_ctor_set(x_29, 6, x_22);
lean_ctor_set(x_29, 7, x_27);
lean_ctor_set(x_29, 8, x_28);
lean_ctor_set(x_29, 9, x_28);
lean_ctor_set(x_29, 10, x_23);
lean_ctor_set(x_29, 11, x_23);
lean_ctor_set(x_29, 12, x_27);
lean_ctor_set(x_29, 13, x_23);
lean_ctor_set(x_29, 14, x_27);
lean_ctor_set(x_29, 15, x_27);
lean_ctor_set(x_29, 16, x_24);
lean_ctor_set(x_29, 17, x_25);
lean_inc(x_9);
x_30 = l_Lake_Package_loadFromEnv(x_29, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
lean_ctor_set(x_31, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_30, 0, x_40);
return x_30;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_44 = x_31;
} else {
 lean_dec_ref(x_31);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_9);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_9);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_30, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_30;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_31, 0);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_30, 0, x_53);
return x_30;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_57 = x_31;
} else {
 lean_dec_ref(x_31);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_14, 17);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 19);
lean_inc(x_65);
x_66 = lean_ctor_get(x_20, 0);
lean_inc(x_66);
lean_dec(x_20);
x_67 = l_Lake_loadLeanConfig___closed__1;
x_68 = l_Lake_loadLeanConfig___closed__3;
x_69 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_69, 0, x_18);
lean_ctor_set(x_69, 1, x_17);
lean_ctor_set(x_69, 2, x_14);
lean_ctor_set(x_69, 3, x_19);
lean_ctor_set(x_69, 4, x_66);
lean_ctor_set(x_69, 5, x_21);
lean_ctor_set(x_69, 6, x_22);
lean_ctor_set(x_69, 7, x_67);
lean_ctor_set(x_69, 8, x_68);
lean_ctor_set(x_69, 9, x_68);
lean_ctor_set(x_69, 10, x_23);
lean_ctor_set(x_69, 11, x_23);
lean_ctor_set(x_69, 12, x_67);
lean_ctor_set(x_69, 13, x_23);
lean_ctor_set(x_69, 14, x_67);
lean_ctor_set(x_69, 15, x_67);
lean_ctor_set(x_69, 16, x_64);
lean_ctor_set(x_69, 17, x_65);
lean_inc(x_9);
x_70 = l_Lake_Package_loadFromEnv(x_69, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_9);
lean_ctor_set(x_71, 0, x_76);
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_9);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_70, 0, x_80);
return x_70;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_70, 1);
lean_inc(x_81);
lean_dec(x_70);
x_82 = lean_ctor_get(x_71, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_84 = x_71;
} else {
 lean_dec_ref(x_71);
 x_84 = lean_box(0);
}
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_9);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_9);
x_88 = !lean_is_exclusive(x_70);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_70, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_71);
if (x_90 == 0)
{
return x_70;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_71, 0);
x_92 = lean_ctor_get(x_71, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_71);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_70, 0, x_93);
return x_70;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_70, 1);
lean_inc(x_94);
lean_dec(x_70);
x_95 = lean_ctor_get(x_71, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_71, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_97 = x_71;
} else {
 lean_dec_ref(x_71);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_9);
x_100 = !lean_is_exclusive(x_70);
if (x_100 == 0)
{
return x_70;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_70, 0);
x_102 = lean_ctor_get(x_70, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_70);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_12);
if (x_104 == 0)
{
lean_object* x_105; 
if (lean_is_scalar(x_7)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_7;
}
lean_ctor_set(x_105, 0, x_12);
lean_ctor_set(x_105, 1, x_13);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_12, 0);
x_107 = lean_ctor_get(x_12, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_12);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_7)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_7;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_13);
return x_109;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_197; lean_object* x_198; 
x_122 = lean_ctor_get(x_5, 0);
x_123 = lean_ctor_get(x_5, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_5);
x_124 = lean_ctor_get(x_1, 6);
lean_inc(x_124);
lean_inc(x_122);
x_197 = l_Lake_PackageConfig_loadFromEnv(x_122, x_124);
x_198 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_197, x_6);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_123);
x_125 = x_201;
x_126 = x_200;
goto block_196;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 1);
lean_inc(x_203);
lean_dec(x_198);
x_204 = lean_io_error_to_string(x_202);
x_205 = 3;
x_206 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set_uint8(x_206, sizeof(void*)*1, x_205);
x_207 = lean_array_get_size(x_123);
x_208 = lean_array_push(x_123, x_206);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_125 = x_209;
x_126 = x_203;
goto block_196;
}
block_196:
{
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_7);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_ctor_get(x_1, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 3);
lean_inc(x_130);
x_131 = l_System_FilePath_join(x_129, x_130);
x_132 = lean_ctor_get(x_1, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 7);
lean_inc(x_134);
x_135 = lean_ctor_get(x_1, 8);
lean_inc(x_135);
lean_dec(x_1);
x_136 = lean_box(0);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = lean_ctor_get(x_127, 17);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 19);
lean_inc(x_138);
x_139 = l_Lake_defaultManifestFile;
x_140 = l_Lake_loadLeanConfig___closed__1;
x_141 = l_Lake_loadLeanConfig___closed__3;
x_142 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_130);
lean_ctor_set(x_142, 2, x_127);
lean_ctor_set(x_142, 3, x_132);
lean_ctor_set(x_142, 4, x_139);
lean_ctor_set(x_142, 5, x_134);
lean_ctor_set(x_142, 6, x_135);
lean_ctor_set(x_142, 7, x_140);
lean_ctor_set(x_142, 8, x_141);
lean_ctor_set(x_142, 9, x_141);
lean_ctor_set(x_142, 10, x_136);
lean_ctor_set(x_142, 11, x_136);
lean_ctor_set(x_142, 12, x_140);
lean_ctor_set(x_142, 13, x_136);
lean_ctor_set(x_142, 14, x_140);
lean_ctor_set(x_142, 15, x_140);
lean_ctor_set(x_142, 16, x_137);
lean_ctor_set(x_142, 17, x_138);
lean_inc(x_122);
x_143 = l_Lake_Package_loadFromEnv(x_142, x_122, x_124, x_128, x_126);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_149 = x_144;
} else {
 lean_dec_ref(x_144);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_122);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
if (lean_is_scalar(x_146)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_146;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_145);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_122);
x_153 = lean_ctor_get(x_143, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_154 = x_143;
} else {
 lean_dec_ref(x_143);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_144, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_144, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_157 = x_144;
} else {
 lean_dec_ref(x_144);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_154;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_153);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_122);
x_160 = lean_ctor_get(x_143, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_143, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_162 = x_143;
} else {
 lean_dec_ref(x_143);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_127, 17);
lean_inc(x_164);
x_165 = lean_ctor_get(x_127, 19);
lean_inc(x_165);
x_166 = lean_ctor_get(x_133, 0);
lean_inc(x_166);
lean_dec(x_133);
x_167 = l_Lake_loadLeanConfig___closed__1;
x_168 = l_Lake_loadLeanConfig___closed__3;
x_169 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_169, 0, x_131);
lean_ctor_set(x_169, 1, x_130);
lean_ctor_set(x_169, 2, x_127);
lean_ctor_set(x_169, 3, x_132);
lean_ctor_set(x_169, 4, x_166);
lean_ctor_set(x_169, 5, x_134);
lean_ctor_set(x_169, 6, x_135);
lean_ctor_set(x_169, 7, x_167);
lean_ctor_set(x_169, 8, x_168);
lean_ctor_set(x_169, 9, x_168);
lean_ctor_set(x_169, 10, x_136);
lean_ctor_set(x_169, 11, x_136);
lean_ctor_set(x_169, 12, x_167);
lean_ctor_set(x_169, 13, x_136);
lean_ctor_set(x_169, 14, x_167);
lean_ctor_set(x_169, 15, x_167);
lean_ctor_set(x_169, 16, x_164);
lean_ctor_set(x_169, 17, x_165);
lean_inc(x_122);
x_170 = l_Lake_Package_loadFromEnv(x_169, x_122, x_124, x_128, x_126);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_122);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
if (lean_is_scalar(x_173)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_173;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_172);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_122);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_171, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_171, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_184 = x_171;
} else {
 lean_dec_ref(x_171);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_180);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_122);
x_187 = lean_ctor_get(x_170, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_170, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_189 = x_170;
} else {
 lean_dec_ref(x_170);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_1);
x_191 = lean_ctor_get(x_125, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_125, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_193 = x_125;
} else {
 lean_dec_ref(x_125);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
if (lean_is_scalar(x_7)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_7;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_126);
return x_195;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_4);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_4, 0);
lean_dec(x_211);
x_212 = !lean_is_exclusive(x_5);
if (x_212 == 0)
{
return x_4;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_5, 0);
x_214 = lean_ctor_get(x_5, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_5);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_4, 0, x_215);
return x_4;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_4, 1);
lean_inc(x_216);
lean_dec(x_4);
x_217 = lean_ctor_get(x_5, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_5, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_219 = x_5;
} else {
 lean_dec_ref(x_5);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_216);
return x_221;
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
