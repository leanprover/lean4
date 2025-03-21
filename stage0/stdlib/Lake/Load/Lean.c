// Lean compiler output
// Module: Lake.Load.Lean
// Imports: Lake.Load.Lean.Elab Lake.Load.Lean.Eval
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_loadLeanConfig___closed__3;
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_PackageDecl_loadFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_loadLeanConfig___closed__4;
static size_t l_Lake_loadLeanConfig___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_loadLeanConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_loadLeanConfig___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__5(lean_object*, lean_object*);
lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_Name_quickCmp(x_3, x_11);
switch (x_14) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_10, x_3, x_4);
x_16 = 0;
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_16);
return x_2;
}
case 1:
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = 0;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_13, x_3, x_4);
x_19 = 0;
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = l_Lean_Name_quickCmp(x_3, x_21);
switch (x_24) {
case 0:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_20, x_3, x_4);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
case 1:
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_4);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
default: 
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_23, x_3, x_4);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = l_Lean_Name_quickCmp(x_3, x_35);
switch (x_38) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_34, x_3, x_4);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_39, 3);
lean_dec(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_dec(x_45);
lean_ctor_set(x_39, 0, x_42);
x_46 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_46);
return x_2;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_ctor_get(x_39, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_40);
x_50 = 1;
lean_ctor_set(x_2, 0, x_49);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_50);
return x_2;
}
}
else
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_39, 1);
x_54 = lean_ctor_get(x_39, 2);
x_55 = lean_ctor_get(x_39, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
x_60 = lean_ctor_get(x_42, 2);
x_61 = lean_ctor_get(x_42, 3);
x_62 = 1;
lean_ctor_set(x_42, 3, x_58);
lean_ctor_set(x_42, 2, x_54);
lean_ctor_set(x_42, 1, x_53);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_62);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_61);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_62);
x_63 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_60);
lean_ctor_set(x_2, 1, x_59);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_63);
return x_2;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_42, 0);
x_65 = lean_ctor_get(x_42, 1);
x_66 = lean_ctor_get(x_42, 2);
x_67 = lean_ctor_get(x_42, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_42);
x_68 = 1;
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_54);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_68);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_67);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_68);
x_70 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_66);
lean_ctor_set(x_2, 1, x_65);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_70);
return x_2;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_71 = lean_ctor_get(x_39, 1);
x_72 = lean_ctor_get(x_39, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_39);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_42, 3);
lean_inc(x_76);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_77 = x_42;
} else {
 lean_dec_ref(x_42);
 x_77 = lean_box(0);
}
x_78 = 1;
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 4, 1);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_35);
lean_ctor_set(x_80, 2, x_36);
lean_ctor_set(x_80, 3, x_37);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_78);
x_81 = 0;
lean_ctor_set(x_2, 3, x_80);
lean_ctor_set(x_2, 2, x_75);
lean_ctor_set(x_2, 1, x_74);
lean_ctor_set(x_2, 0, x_79);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_81);
return x_2;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_2);
x_82 = !lean_is_exclusive(x_42);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_42, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_42, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_42, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_42, 0);
lean_dec(x_86);
x_87 = 1;
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_87);
return x_42;
}
else
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_42);
x_88 = 1;
x_89 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_89, 0, x_39);
lean_ctor_set(x_89, 1, x_35);
lean_ctor_set(x_89, 2, x_36);
lean_ctor_set(x_89, 3, x_37);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_39);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_39, 1);
x_93 = lean_ctor_get(x_39, 2);
x_94 = lean_ctor_get(x_39, 3);
x_95 = lean_ctor_get(x_39, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
uint8_t x_97; uint8_t x_98; 
x_97 = 1;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_97);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_97);
x_98 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_41);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_98);
return x_2;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_41, 0);
x_100 = lean_ctor_get(x_41, 1);
x_101 = lean_ctor_get(x_41, 2);
x_102 = lean_ctor_get(x_41, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_41);
x_103 = 1;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_103);
x_105 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_104);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_105);
return x_2;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_106 = lean_ctor_get(x_39, 1);
x_107 = lean_ctor_get(x_39, 2);
x_108 = lean_ctor_get(x_39, 3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_39);
x_109 = lean_ctor_get(x_41, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_41, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_41, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_41, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_113 = x_41;
} else {
 lean_dec_ref(x_41);
 x_113 = lean_box(0);
}
x_114 = 1;
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(1, 4, 1);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set(x_115, 2, x_111);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_114);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_35);
lean_ctor_set(x_116, 2, x_36);
lean_ctor_set(x_116, 3, x_37);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_114);
x_117 = 0;
lean_ctor_set(x_2, 3, x_116);
lean_ctor_set(x_2, 2, x_107);
lean_ctor_set(x_2, 1, x_106);
lean_ctor_set(x_2, 0, x_115);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_117);
return x_2;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_39, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_free_object(x_2);
x_119 = !lean_is_exclusive(x_41);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_41, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_41, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_41, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_41, 0);
lean_dec(x_123);
x_124 = 1;
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_124);
return x_41;
}
else
{
uint8_t x_125; lean_object* x_126; 
lean_dec(x_41);
x_125 = 1;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_35);
lean_ctor_set(x_126, 2, x_36);
lean_ctor_set(x_126, 3, x_37);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_2);
x_128 = !lean_is_exclusive(x_39);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_39, 1);
x_130 = lean_ctor_get(x_39, 2);
x_131 = lean_ctor_get(x_39, 3);
lean_dec(x_131);
x_132 = lean_ctor_get(x_39, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_118);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_118, 0);
x_135 = lean_ctor_get(x_118, 1);
x_136 = lean_ctor_get(x_118, 2);
x_137 = lean_ctor_get(x_118, 3);
x_138 = 1;
lean_inc(x_41);
lean_ctor_set(x_118, 3, x_134);
lean_ctor_set(x_118, 2, x_130);
lean_ctor_set(x_118, 1, x_129);
lean_ctor_set(x_118, 0, x_41);
x_139 = !lean_is_exclusive(x_41);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_41, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_41, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_41, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_41, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_137);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_138);
x_144 = 0;
lean_ctor_set(x_39, 3, x_41);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_144);
return x_39;
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_41);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_35);
lean_ctor_set(x_145, 2, x_36);
lean_ctor_set(x_145, 3, x_37);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_138);
x_146 = 0;
lean_ctor_set(x_39, 3, x_145);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_146);
return x_39;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_147 = lean_ctor_get(x_118, 0);
x_148 = lean_ctor_get(x_118, 1);
x_149 = lean_ctor_get(x_118, 2);
x_150 = lean_ctor_get(x_118, 3);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_118);
x_151 = 1;
lean_inc(x_41);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_41);
lean_ctor_set(x_152, 1, x_129);
lean_ctor_set(x_152, 2, x_130);
lean_ctor_set(x_152, 3, x_147);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_153 = x_41;
} else {
 lean_dec_ref(x_41);
 x_153 = lean_box(0);
}
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_151);
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 4, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_35);
lean_ctor_set(x_154, 2, x_36);
lean_ctor_set(x_154, 3, x_37);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_151);
x_155 = 0;
lean_ctor_set(x_39, 3, x_154);
lean_ctor_set(x_39, 2, x_149);
lean_ctor_set(x_39, 1, x_148);
lean_ctor_set(x_39, 0, x_152);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_155);
return x_39;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_39, 1);
x_157 = lean_ctor_get(x_39, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_39);
x_158 = lean_ctor_get(x_118, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_118, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_118, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_118, 3);
lean_inc(x_161);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_162 = x_118;
} else {
 lean_dec_ref(x_118);
 x_162 = lean_box(0);
}
x_163 = 1;
lean_inc(x_41);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_41);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_157);
lean_ctor_set(x_164, 3, x_158);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_165 = x_41;
} else {
 lean_dec_ref(x_41);
 x_165 = lean_box(0);
}
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_163);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_35);
lean_ctor_set(x_166, 2, x_36);
lean_ctor_set(x_166, 3, x_37);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_163);
x_167 = 0;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_160);
lean_ctor_set(x_168, 3, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_39);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_39, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_39, 0);
lean_dec(x_171);
x_172 = !lean_is_exclusive(x_41);
if (x_172 == 0)
{
uint8_t x_173; 
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_173 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_173);
return x_2;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_41, 0);
x_175 = lean_ctor_get(x_41, 1);
x_176 = lean_ctor_get(x_41, 2);
x_177 = lean_ctor_get(x_41, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_41);
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
lean_ctor_set(x_39, 0, x_178);
x_179 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_179);
return x_2;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_180 = lean_ctor_get(x_39, 1);
x_181 = lean_ctor_get(x_39, 2);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_39);
x_182 = lean_ctor_get(x_41, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_41, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_41, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_41, 3);
lean_inc(x_185);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_186 = x_41;
} else {
 lean_dec_ref(x_41);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 4, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set(x_187, 2, x_184);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_127);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_181);
lean_ctor_set(x_188, 3, x_118);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_40);
x_189 = 1;
lean_ctor_set(x_2, 0, x_188);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_189);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_190; 
x_190 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_190);
return x_2;
}
}
case 1:
{
uint8_t x_191; 
lean_dec(x_36);
lean_dec(x_35);
x_191 = 1;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_191);
return x_2;
}
default: 
{
lean_object* x_192; uint8_t x_193; 
x_192 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_37, x_3, x_4);
x_193 = lean_ctor_get_uint8(x_192, sizeof(void*)*4);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_192, 3);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_192);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_ctor_get(x_192, 3);
lean_dec(x_197);
x_198 = lean_ctor_get(x_192, 0);
lean_dec(x_198);
lean_ctor_set(x_192, 0, x_195);
x_199 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_199);
return x_2;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_192, 1);
x_201 = lean_ctor_get(x_192, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_195);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_195);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_193);
x_203 = 1;
lean_ctor_set(x_2, 3, x_202);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_203);
return x_2;
}
}
else
{
uint8_t x_204; 
x_204 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_192);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_192, 1);
x_207 = lean_ctor_get(x_192, 2);
x_208 = lean_ctor_get(x_192, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_192, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_195);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_216; 
x_211 = lean_ctor_get(x_195, 0);
x_212 = lean_ctor_get(x_195, 1);
x_213 = lean_ctor_get(x_195, 2);
x_214 = lean_ctor_get(x_195, 3);
x_215 = 1;
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_215);
lean_ctor_set(x_192, 3, x_214);
lean_ctor_set(x_192, 2, x_213);
lean_ctor_set(x_192, 1, x_212);
lean_ctor_set(x_192, 0, x_211);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_215);
x_216 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_216);
return x_2;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint8_t x_223; 
x_217 = lean_ctor_get(x_195, 0);
x_218 = lean_ctor_get(x_195, 1);
x_219 = lean_ctor_get(x_195, 2);
x_220 = lean_ctor_get(x_195, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_195);
x_221 = 1;
x_222 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_222, 0, x_34);
lean_ctor_set(x_222, 1, x_35);
lean_ctor_set(x_222, 2, x_36);
lean_ctor_set(x_222, 3, x_194);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_221);
lean_ctor_set(x_192, 3, x_220);
lean_ctor_set(x_192, 2, x_219);
lean_ctor_set(x_192, 1, x_218);
lean_ctor_set(x_192, 0, x_217);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_221);
x_223 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_223);
return x_2;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_224 = lean_ctor_get(x_192, 1);
x_225 = lean_ctor_get(x_192, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_192);
x_226 = lean_ctor_get(x_195, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_195, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_195, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_195, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_230 = x_195;
} else {
 lean_dec_ref(x_195);
 x_230 = lean_box(0);
}
x_231 = 1;
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(1, 4, 1);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_34);
lean_ctor_set(x_232, 1, x_35);
lean_ctor_set(x_232, 2, x_36);
lean_ctor_set(x_232, 3, x_194);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
x_233 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_229);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_231);
x_234 = 0;
lean_ctor_set(x_2, 3, x_233);
lean_ctor_set(x_2, 2, x_225);
lean_ctor_set(x_2, 1, x_224);
lean_ctor_set(x_2, 0, x_232);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_234);
return x_2;
}
}
else
{
uint8_t x_235; 
lean_free_object(x_2);
x_235 = !lean_is_exclusive(x_195);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_195, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_195, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_195, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_195, 0);
lean_dec(x_239);
x_240 = 1;
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_240);
return x_195;
}
else
{
uint8_t x_241; lean_object* x_242; 
lean_dec(x_195);
x_241 = 1;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_34);
lean_ctor_set(x_242, 1, x_35);
lean_ctor_set(x_242, 2, x_36);
lean_ctor_set(x_242, 3, x_192);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
return x_242;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_192);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_192, 0);
lean_dec(x_245);
x_246 = !lean_is_exclusive(x_194);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_194, 0);
x_248 = lean_ctor_get(x_194, 1);
x_249 = lean_ctor_get(x_194, 2);
x_250 = lean_ctor_get(x_194, 3);
x_251 = 1;
lean_ctor_set(x_194, 3, x_247);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_251);
lean_ctor_set(x_192, 0, x_250);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_249);
lean_ctor_set(x_2, 1, x_248);
lean_ctor_set(x_2, 0, x_194);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_252);
return x_2;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_194, 0);
x_254 = lean_ctor_get(x_194, 1);
x_255 = lean_ctor_get(x_194, 2);
x_256 = lean_ctor_get(x_194, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_194);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_34);
lean_ctor_set(x_258, 1, x_35);
lean_ctor_set(x_258, 2, x_36);
lean_ctor_set(x_258, 3, x_253);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_192, 0, x_256);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_255);
lean_ctor_set(x_2, 1, x_254);
lean_ctor_set(x_2, 0, x_258);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_259);
return x_2;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_192, 1);
x_261 = lean_ctor_get(x_192, 2);
x_262 = lean_ctor_get(x_192, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_192);
x_263 = lean_ctor_get(x_194, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_194, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_194, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_194, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_267 = x_194;
} else {
 lean_dec_ref(x_194);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_34);
lean_ctor_set(x_269, 1, x_35);
lean_ctor_set(x_269, 2, x_36);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_260);
lean_ctor_set(x_270, 2, x_261);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_2, 3, x_270);
lean_ctor_set(x_2, 2, x_265);
lean_ctor_set(x_2, 1, x_264);
lean_ctor_set(x_2, 0, x_269);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_271);
return x_2;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_192, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_2);
x_273 = !lean_is_exclusive(x_194);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_194, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_194, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_194, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_194, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_194, 3, x_192);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_278);
return x_194;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_194);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_34);
lean_ctor_set(x_280, 1, x_35);
lean_ctor_set(x_280, 2, x_36);
lean_ctor_set(x_280, 3, x_192);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_2);
x_282 = !lean_is_exclusive(x_192);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_192, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_192, 0);
lean_dec(x_284);
x_285 = !lean_is_exclusive(x_272);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_291; 
x_286 = lean_ctor_get(x_272, 0);
x_287 = lean_ctor_get(x_272, 1);
x_288 = lean_ctor_get(x_272, 2);
x_289 = lean_ctor_get(x_272, 3);
x_290 = 1;
lean_inc(x_194);
lean_ctor_set(x_272, 3, x_194);
lean_ctor_set(x_272, 2, x_36);
lean_ctor_set(x_272, 1, x_35);
lean_ctor_set(x_272, 0, x_34);
x_291 = !lean_is_exclusive(x_194);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_292 = lean_ctor_get(x_194, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_194, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_194, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_194, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
lean_ctor_set(x_194, 3, x_289);
lean_ctor_set(x_194, 2, x_288);
lean_ctor_set(x_194, 1, x_287);
lean_ctor_set(x_194, 0, x_286);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_290);
x_296 = 0;
lean_ctor_set(x_192, 3, x_194);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_296);
return x_192;
}
else
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_194);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_287);
lean_ctor_set(x_297, 2, x_288);
lean_ctor_set(x_297, 3, x_289);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_290);
x_298 = 0;
lean_ctor_set(x_192, 3, x_297);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_298);
return x_192;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_ctor_get(x_272, 0);
x_300 = lean_ctor_get(x_272, 1);
x_301 = lean_ctor_get(x_272, 2);
x_302 = lean_ctor_get(x_272, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_272);
x_303 = 1;
lean_inc(x_194);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_34);
lean_ctor_set(x_304, 1, x_35);
lean_ctor_set(x_304, 2, x_36);
lean_ctor_set(x_304, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_305 = x_194;
} else {
 lean_dec_ref(x_194);
 x_305 = lean_box(0);
}
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_303);
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 4, 1);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_299);
lean_ctor_set(x_306, 1, x_300);
lean_ctor_set(x_306, 2, x_301);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_303);
x_307 = 0;
lean_ctor_set(x_192, 3, x_306);
lean_ctor_set(x_192, 0, x_304);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_307);
return x_192;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; 
x_308 = lean_ctor_get(x_192, 1);
x_309 = lean_ctor_get(x_192, 2);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_192);
x_310 = lean_ctor_get(x_272, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_272, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_272, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 3);
lean_inc(x_313);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_314 = x_272;
} else {
 lean_dec_ref(x_272);
 x_314 = lean_box(0);
}
x_315 = 1;
lean_inc(x_194);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(1, 4, 1);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_34);
lean_ctor_set(x_316, 1, x_35);
lean_ctor_set(x_316, 2, x_36);
lean_ctor_set(x_316, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_317 = x_194;
} else {
 lean_dec_ref(x_194);
 x_317 = lean_box(0);
}
lean_ctor_set_uint8(x_316, sizeof(void*)*4, x_315);
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_310);
lean_ctor_set(x_318, 1, x_311);
lean_ctor_set(x_318, 2, x_312);
lean_ctor_set(x_318, 3, x_313);
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_315);
x_319 = 0;
x_320 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_308);
lean_ctor_set(x_320, 2, x_309);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_319);
return x_320;
}
}
else
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_192);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_192, 3);
lean_dec(x_322);
x_323 = lean_ctor_get(x_192, 0);
lean_dec(x_323);
x_324 = !lean_is_exclusive(x_194);
if (x_324 == 0)
{
uint8_t x_325; 
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_281);
x_325 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_325);
return x_2;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_326 = lean_ctor_get(x_194, 0);
x_327 = lean_ctor_get(x_194, 1);
x_328 = lean_ctor_get(x_194, 2);
x_329 = lean_ctor_get(x_194, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_194);
x_330 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_328);
lean_ctor_set(x_330, 3, x_329);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_281);
lean_ctor_set(x_192, 0, x_330);
x_331 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_331);
return x_2;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_332 = lean_ctor_get(x_192, 1);
x_333 = lean_ctor_get(x_192, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_192);
x_334 = lean_ctor_get(x_194, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_194, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_194, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_194, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_338 = x_194;
} else {
 lean_dec_ref(x_194);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 4, 1);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_334);
lean_ctor_set(x_339, 1, x_335);
lean_ctor_set(x_339, 2, x_336);
lean_ctor_set(x_339, 3, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_281);
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
lean_ctor_set(x_340, 2, x_333);
lean_ctor_set(x_340, 3, x_272);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_193);
x_341 = 1;
lean_ctor_set(x_2, 3, x_340);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_341);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_342; 
x_342 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_342);
return x_2;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_343 = lean_ctor_get(x_2, 0);
x_344 = lean_ctor_get(x_2, 1);
x_345 = lean_ctor_get(x_2, 2);
x_346 = lean_ctor_get(x_2, 3);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_2);
x_347 = l_Lean_Name_quickCmp(x_3, x_344);
switch (x_347) {
case 0:
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_343, x_3, x_4);
x_349 = lean_ctor_get_uint8(x_348, sizeof(void*)*4);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_348, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; 
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_354 = x_348;
} else {
 lean_dec_ref(x_348);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 4, 1);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_353);
lean_ctor_set(x_355, 3, x_351);
lean_ctor_set_uint8(x_355, sizeof(void*)*4, x_349);
x_356 = 1;
x_357 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_344);
lean_ctor_set(x_357, 2, x_345);
lean_ctor_set(x_357, 3, x_346);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_356);
return x_357;
}
else
{
uint8_t x_358; 
x_358 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; 
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_361 = x_348;
} else {
 lean_dec_ref(x_348);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_351, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 3);
lean_inc(x_365);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_366 = x_351;
} else {
 lean_dec_ref(x_351);
 x_366 = lean_box(0);
}
x_367 = 1;
if (lean_is_scalar(x_366)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_366;
}
lean_ctor_set(x_368, 0, x_350);
lean_ctor_set(x_368, 1, x_359);
lean_ctor_set(x_368, 2, x_360);
lean_ctor_set(x_368, 3, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_361)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_361;
}
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_344);
lean_ctor_set(x_369, 2, x_345);
lean_ctor_set(x_369, 3, x_346);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_367);
x_370 = 0;
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_363);
lean_ctor_set(x_371, 2, x_364);
lean_ctor_set(x_371, 3, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
return x_371;
}
else
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_372 = x_351;
} else {
 lean_dec_ref(x_351);
 x_372 = lean_box(0);
}
x_373 = 1;
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_348);
lean_ctor_set(x_374, 1, x_344);
lean_ctor_set(x_374, 2, x_345);
lean_ctor_set(x_374, 3, x_346);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; 
x_376 = lean_ctor_get(x_348, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_348, 2);
lean_inc(x_377);
x_378 = lean_ctor_get(x_348, 3);
lean_inc(x_378);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_379 = x_348;
} else {
 lean_dec_ref(x_348);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_350, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_350, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_350, 2);
lean_inc(x_382);
x_383 = lean_ctor_get(x_350, 3);
lean_inc(x_383);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_384 = x_350;
} else {
 lean_dec_ref(x_350);
 x_384 = lean_box(0);
}
x_385 = 1;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_381);
lean_ctor_set(x_386, 2, x_382);
lean_ctor_set(x_386, 3, x_383);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
if (lean_is_scalar(x_379)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_379;
}
lean_ctor_set(x_387, 0, x_378);
lean_ctor_set(x_387, 1, x_344);
lean_ctor_set(x_387, 2, x_345);
lean_ctor_set(x_387, 3, x_346);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_385);
x_388 = 0;
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_376);
lean_ctor_set(x_389, 2, x_377);
lean_ctor_set(x_389, 3, x_387);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
return x_389;
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_348, 3);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_391 = x_350;
} else {
 lean_dec_ref(x_350);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_348);
lean_ctor_set(x_393, 1, x_344);
lean_ctor_set(x_393, 2, x_345);
lean_ctor_set(x_393, 3, x_346);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
return x_393;
}
else
{
uint8_t x_394; 
x_394 = lean_ctor_get_uint8(x_390, sizeof(void*)*4);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_348, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_348, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_397 = x_348;
} else {
 lean_dec_ref(x_348);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_390, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_390, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_390, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_390, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 x_402 = x_390;
} else {
 lean_dec_ref(x_390);
 x_402 = lean_box(0);
}
x_403 = 1;
lean_inc(x_350);
if (lean_is_scalar(x_402)) {
 x_404 = lean_alloc_ctor(1, 4, 1);
} else {
 x_404 = x_402;
}
lean_ctor_set(x_404, 0, x_350);
lean_ctor_set(x_404, 1, x_395);
lean_ctor_set(x_404, 2, x_396);
lean_ctor_set(x_404, 3, x_398);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_405 = x_350;
} else {
 lean_dec_ref(x_350);
 x_405 = lean_box(0);
}
lean_ctor_set_uint8(x_404, sizeof(void*)*4, x_403);
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 4, 1);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_401);
lean_ctor_set(x_406, 1, x_344);
lean_ctor_set(x_406, 2, x_345);
lean_ctor_set(x_406, 3, x_346);
lean_ctor_set_uint8(x_406, sizeof(void*)*4, x_403);
x_407 = 0;
if (lean_is_scalar(x_397)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_397;
}
lean_ctor_set(x_408, 0, x_404);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_408, 2, x_400);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_409 = lean_ctor_get(x_348, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_348, 2);
lean_inc(x_410);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_411 = x_348;
} else {
 lean_dec_ref(x_348);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_350, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_350, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_350, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_350, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_416 = x_350;
} else {
 lean_dec_ref(x_350);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_413);
lean_ctor_set(x_417, 2, x_414);
lean_ctor_set(x_417, 3, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_411)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_411;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_409);
lean_ctor_set(x_418, 2, x_410);
lean_ctor_set(x_418, 3, x_390);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_349);
x_419 = 1;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_344);
lean_ctor_set(x_420, 2, x_345);
lean_ctor_set(x_420, 3, x_346);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
}
}
}
}
else
{
uint8_t x_421; lean_object* x_422; 
x_421 = 1;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_348);
lean_ctor_set(x_422, 1, x_344);
lean_ctor_set(x_422, 2, x_345);
lean_ctor_set(x_422, 3, x_346);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
}
case 1:
{
uint8_t x_423; lean_object* x_424; 
lean_dec(x_345);
lean_dec(x_344);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_343);
lean_ctor_set(x_424, 1, x_3);
lean_ctor_set(x_424, 2, x_4);
lean_ctor_set(x_424, 3, x_346);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
default: 
{
lean_object* x_425; uint8_t x_426; 
x_425 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_346, x_3, x_4);
x_426 = lean_ctor_get_uint8(x_425, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_425, 3);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; 
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_425, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_431 = x_425;
} else {
 lean_dec_ref(x_425);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 4, 1);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_430);
lean_ctor_set(x_432, 3, x_428);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_426);
x_433 = 1;
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_343);
lean_ctor_set(x_434, 1, x_344);
lean_ctor_set(x_434, 2, x_345);
lean_ctor_set(x_434, 3, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_433);
return x_434;
}
else
{
uint8_t x_435; 
x_435 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; 
x_436 = lean_ctor_get(x_425, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_425, 2);
lean_inc(x_437);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_438 = x_425;
} else {
 lean_dec_ref(x_425);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_428, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_428, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_428, 3);
lean_inc(x_442);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_443 = x_428;
} else {
 lean_dec_ref(x_428);
 x_443 = lean_box(0);
}
x_444 = 1;
if (lean_is_scalar(x_443)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_443;
}
lean_ctor_set(x_445, 0, x_343);
lean_ctor_set(x_445, 1, x_344);
lean_ctor_set(x_445, 2, x_345);
lean_ctor_set(x_445, 3, x_427);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_438)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_438;
}
lean_ctor_set(x_446, 0, x_439);
lean_ctor_set(x_446, 1, x_440);
lean_ctor_set(x_446, 2, x_441);
lean_ctor_set(x_446, 3, x_442);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_444);
x_447 = 0;
x_448 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_436);
lean_ctor_set(x_448, 2, x_437);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
return x_448;
}
else
{
lean_object* x_449; uint8_t x_450; lean_object* x_451; 
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_449 = x_428;
} else {
 lean_dec_ref(x_428);
 x_449 = lean_box(0);
}
x_450 = 1;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_343);
lean_ctor_set(x_451, 1, x_344);
lean_ctor_set(x_451, 2, x_345);
lean_ctor_set(x_451, 3, x_425);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
x_452 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; 
x_453 = lean_ctor_get(x_425, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_425, 2);
lean_inc(x_454);
x_455 = lean_ctor_get(x_425, 3);
lean_inc(x_455);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_456 = x_425;
} else {
 lean_dec_ref(x_425);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_427, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_427, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_427, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_427, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_461 = x_427;
} else {
 lean_dec_ref(x_427);
 x_461 = lean_box(0);
}
x_462 = 1;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_343);
lean_ctor_set(x_463, 1, x_344);
lean_ctor_set(x_463, 2, x_345);
lean_ctor_set(x_463, 3, x_457);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
if (lean_is_scalar(x_456)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_456;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_453);
lean_ctor_set(x_464, 2, x_454);
lean_ctor_set(x_464, 3, x_455);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_462);
x_465 = 0;
x_466 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_458);
lean_ctor_set(x_466, 2, x_459);
lean_ctor_set(x_466, 3, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
return x_466;
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_425, 3);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; uint8_t x_469; lean_object* x_470; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_468 = x_427;
} else {
 lean_dec_ref(x_427);
 x_468 = lean_box(0);
}
x_469 = 1;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_343);
lean_ctor_set(x_470, 1, x_344);
lean_ctor_set(x_470, 2, x_345);
lean_ctor_set(x_470, 3, x_425);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
return x_470;
}
else
{
uint8_t x_471; 
x_471 = lean_ctor_get_uint8(x_467, sizeof(void*)*4);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; 
x_472 = lean_ctor_get(x_425, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_425, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_474 = x_425;
} else {
 lean_dec_ref(x_425);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_467, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_467, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_467, 2);
lean_inc(x_477);
x_478 = lean_ctor_get(x_467, 3);
lean_inc(x_478);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 x_479 = x_467;
} else {
 lean_dec_ref(x_467);
 x_479 = lean_box(0);
}
x_480 = 1;
lean_inc(x_427);
if (lean_is_scalar(x_479)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_479;
}
lean_ctor_set(x_481, 0, x_343);
lean_ctor_set(x_481, 1, x_344);
lean_ctor_set(x_481, 2, x_345);
lean_ctor_set(x_481, 3, x_427);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_482 = x_427;
} else {
 lean_dec_ref(x_427);
 x_482 = lean_box(0);
}
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_480);
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_475);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_478);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_480);
x_484 = 0;
if (lean_is_scalar(x_474)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_474;
}
lean_ctor_set(x_485, 0, x_481);
lean_ctor_set(x_485, 1, x_472);
lean_ctor_set(x_485, 2, x_473);
lean_ctor_set(x_485, 3, x_483);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; 
x_486 = lean_ctor_get(x_425, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_425, 2);
lean_inc(x_487);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_488 = x_425;
} else {
 lean_dec_ref(x_425);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_427, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_427, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_427, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_427, 3);
lean_inc(x_492);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_493 = x_427;
} else {
 lean_dec_ref(x_427);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_490);
lean_ctor_set(x_494, 2, x_491);
lean_ctor_set(x_494, 3, x_492);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_488)) {
 x_495 = lean_alloc_ctor(1, 4, 1);
} else {
 x_495 = x_488;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_486);
lean_ctor_set(x_495, 2, x_487);
lean_ctor_set(x_495, 3, x_467);
lean_ctor_set_uint8(x_495, sizeof(void*)*4, x_426);
x_496 = 1;
x_497 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_497, 0, x_343);
lean_ctor_set(x_497, 1, x_344);
lean_ctor_set(x_497, 2, x_345);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
return x_497;
}
}
}
}
}
else
{
uint8_t x_498; lean_object* x_499; 
x_498 = 1;
x_499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_499, 0, x_343);
lean_ctor_set(x_499, 1, x_344);
lean_ctor_set(x_499, 2, x_345);
lean_ctor_set(x_499, 3, x_425);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_498);
return x_499;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_Name_quickCmp(x_3, x_11);
switch (x_14) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_10, x_3, x_4);
x_16 = 0;
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_16);
return x_2;
}
case 1:
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = 0;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_13, x_3, x_4);
x_19 = 0;
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = l_Lean_Name_quickCmp(x_3, x_21);
switch (x_24) {
case 0:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_20, x_3, x_4);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
case 1:
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_4);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
default: 
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_23, x_3, x_4);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = l_Lean_Name_quickCmp(x_3, x_35);
switch (x_38) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_34, x_3, x_4);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_39, 3);
lean_dec(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_dec(x_45);
lean_ctor_set(x_39, 0, x_42);
x_46 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_46);
return x_2;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_ctor_get(x_39, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_40);
x_50 = 1;
lean_ctor_set(x_2, 0, x_49);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_50);
return x_2;
}
}
else
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_39, 1);
x_54 = lean_ctor_get(x_39, 2);
x_55 = lean_ctor_get(x_39, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
x_60 = lean_ctor_get(x_42, 2);
x_61 = lean_ctor_get(x_42, 3);
x_62 = 1;
lean_ctor_set(x_42, 3, x_58);
lean_ctor_set(x_42, 2, x_54);
lean_ctor_set(x_42, 1, x_53);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_62);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_61);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_62);
x_63 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_60);
lean_ctor_set(x_2, 1, x_59);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_63);
return x_2;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_42, 0);
x_65 = lean_ctor_get(x_42, 1);
x_66 = lean_ctor_get(x_42, 2);
x_67 = lean_ctor_get(x_42, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_42);
x_68 = 1;
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_54);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_68);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_67);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_68);
x_70 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_66);
lean_ctor_set(x_2, 1, x_65);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_70);
return x_2;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_71 = lean_ctor_get(x_39, 1);
x_72 = lean_ctor_get(x_39, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_39);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_42, 3);
lean_inc(x_76);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_77 = x_42;
} else {
 lean_dec_ref(x_42);
 x_77 = lean_box(0);
}
x_78 = 1;
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 4, 1);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_35);
lean_ctor_set(x_80, 2, x_36);
lean_ctor_set(x_80, 3, x_37);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_78);
x_81 = 0;
lean_ctor_set(x_2, 3, x_80);
lean_ctor_set(x_2, 2, x_75);
lean_ctor_set(x_2, 1, x_74);
lean_ctor_set(x_2, 0, x_79);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_81);
return x_2;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_2);
x_82 = !lean_is_exclusive(x_42);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_42, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_42, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_42, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_42, 0);
lean_dec(x_86);
x_87 = 1;
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_87);
return x_42;
}
else
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_42);
x_88 = 1;
x_89 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_89, 0, x_39);
lean_ctor_set(x_89, 1, x_35);
lean_ctor_set(x_89, 2, x_36);
lean_ctor_set(x_89, 3, x_37);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_39);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_39, 1);
x_93 = lean_ctor_get(x_39, 2);
x_94 = lean_ctor_get(x_39, 3);
x_95 = lean_ctor_get(x_39, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
uint8_t x_97; uint8_t x_98; 
x_97 = 1;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_97);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_97);
x_98 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_41);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_98);
return x_2;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_41, 0);
x_100 = lean_ctor_get(x_41, 1);
x_101 = lean_ctor_get(x_41, 2);
x_102 = lean_ctor_get(x_41, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_41);
x_103 = 1;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_103);
x_105 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_104);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_105);
return x_2;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_106 = lean_ctor_get(x_39, 1);
x_107 = lean_ctor_get(x_39, 2);
x_108 = lean_ctor_get(x_39, 3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_39);
x_109 = lean_ctor_get(x_41, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_41, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_41, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_41, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_113 = x_41;
} else {
 lean_dec_ref(x_41);
 x_113 = lean_box(0);
}
x_114 = 1;
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(1, 4, 1);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set(x_115, 2, x_111);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_114);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_35);
lean_ctor_set(x_116, 2, x_36);
lean_ctor_set(x_116, 3, x_37);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_114);
x_117 = 0;
lean_ctor_set(x_2, 3, x_116);
lean_ctor_set(x_2, 2, x_107);
lean_ctor_set(x_2, 1, x_106);
lean_ctor_set(x_2, 0, x_115);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_117);
return x_2;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_39, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_free_object(x_2);
x_119 = !lean_is_exclusive(x_41);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_41, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_41, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_41, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_41, 0);
lean_dec(x_123);
x_124 = 1;
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_124);
return x_41;
}
else
{
uint8_t x_125; lean_object* x_126; 
lean_dec(x_41);
x_125 = 1;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_35);
lean_ctor_set(x_126, 2, x_36);
lean_ctor_set(x_126, 3, x_37);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_2);
x_128 = !lean_is_exclusive(x_39);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_39, 1);
x_130 = lean_ctor_get(x_39, 2);
x_131 = lean_ctor_get(x_39, 3);
lean_dec(x_131);
x_132 = lean_ctor_get(x_39, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_118);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_118, 0);
x_135 = lean_ctor_get(x_118, 1);
x_136 = lean_ctor_get(x_118, 2);
x_137 = lean_ctor_get(x_118, 3);
x_138 = 1;
lean_inc(x_41);
lean_ctor_set(x_118, 3, x_134);
lean_ctor_set(x_118, 2, x_130);
lean_ctor_set(x_118, 1, x_129);
lean_ctor_set(x_118, 0, x_41);
x_139 = !lean_is_exclusive(x_41);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_41, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_41, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_41, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_41, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_137);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_138);
x_144 = 0;
lean_ctor_set(x_39, 3, x_41);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_144);
return x_39;
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_41);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_35);
lean_ctor_set(x_145, 2, x_36);
lean_ctor_set(x_145, 3, x_37);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_138);
x_146 = 0;
lean_ctor_set(x_39, 3, x_145);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_146);
return x_39;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_147 = lean_ctor_get(x_118, 0);
x_148 = lean_ctor_get(x_118, 1);
x_149 = lean_ctor_get(x_118, 2);
x_150 = lean_ctor_get(x_118, 3);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_118);
x_151 = 1;
lean_inc(x_41);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_41);
lean_ctor_set(x_152, 1, x_129);
lean_ctor_set(x_152, 2, x_130);
lean_ctor_set(x_152, 3, x_147);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_153 = x_41;
} else {
 lean_dec_ref(x_41);
 x_153 = lean_box(0);
}
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_151);
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 4, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_35);
lean_ctor_set(x_154, 2, x_36);
lean_ctor_set(x_154, 3, x_37);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_151);
x_155 = 0;
lean_ctor_set(x_39, 3, x_154);
lean_ctor_set(x_39, 2, x_149);
lean_ctor_set(x_39, 1, x_148);
lean_ctor_set(x_39, 0, x_152);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_155);
return x_39;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_39, 1);
x_157 = lean_ctor_get(x_39, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_39);
x_158 = lean_ctor_get(x_118, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_118, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_118, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_118, 3);
lean_inc(x_161);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_162 = x_118;
} else {
 lean_dec_ref(x_118);
 x_162 = lean_box(0);
}
x_163 = 1;
lean_inc(x_41);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_41);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_157);
lean_ctor_set(x_164, 3, x_158);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_165 = x_41;
} else {
 lean_dec_ref(x_41);
 x_165 = lean_box(0);
}
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_163);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_35);
lean_ctor_set(x_166, 2, x_36);
lean_ctor_set(x_166, 3, x_37);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_163);
x_167 = 0;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_160);
lean_ctor_set(x_168, 3, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_39);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_39, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_39, 0);
lean_dec(x_171);
x_172 = !lean_is_exclusive(x_41);
if (x_172 == 0)
{
uint8_t x_173; 
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_173 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_173);
return x_2;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_41, 0);
x_175 = lean_ctor_get(x_41, 1);
x_176 = lean_ctor_get(x_41, 2);
x_177 = lean_ctor_get(x_41, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_41);
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
lean_ctor_set(x_39, 0, x_178);
x_179 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_179);
return x_2;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_180 = lean_ctor_get(x_39, 1);
x_181 = lean_ctor_get(x_39, 2);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_39);
x_182 = lean_ctor_get(x_41, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_41, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_41, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_41, 3);
lean_inc(x_185);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_186 = x_41;
} else {
 lean_dec_ref(x_41);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 4, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set(x_187, 2, x_184);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_127);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_181);
lean_ctor_set(x_188, 3, x_118);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_40);
x_189 = 1;
lean_ctor_set(x_2, 0, x_188);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_189);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_190; 
x_190 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_190);
return x_2;
}
}
case 1:
{
uint8_t x_191; 
lean_dec(x_36);
lean_dec(x_35);
x_191 = 1;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_191);
return x_2;
}
default: 
{
lean_object* x_192; uint8_t x_193; 
x_192 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_37, x_3, x_4);
x_193 = lean_ctor_get_uint8(x_192, sizeof(void*)*4);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_192, 3);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_192);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_ctor_get(x_192, 3);
lean_dec(x_197);
x_198 = lean_ctor_get(x_192, 0);
lean_dec(x_198);
lean_ctor_set(x_192, 0, x_195);
x_199 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_199);
return x_2;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_192, 1);
x_201 = lean_ctor_get(x_192, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_195);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_195);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_193);
x_203 = 1;
lean_ctor_set(x_2, 3, x_202);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_203);
return x_2;
}
}
else
{
uint8_t x_204; 
x_204 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_192);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_192, 1);
x_207 = lean_ctor_get(x_192, 2);
x_208 = lean_ctor_get(x_192, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_192, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_195);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_216; 
x_211 = lean_ctor_get(x_195, 0);
x_212 = lean_ctor_get(x_195, 1);
x_213 = lean_ctor_get(x_195, 2);
x_214 = lean_ctor_get(x_195, 3);
x_215 = 1;
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_215);
lean_ctor_set(x_192, 3, x_214);
lean_ctor_set(x_192, 2, x_213);
lean_ctor_set(x_192, 1, x_212);
lean_ctor_set(x_192, 0, x_211);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_215);
x_216 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_216);
return x_2;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint8_t x_223; 
x_217 = lean_ctor_get(x_195, 0);
x_218 = lean_ctor_get(x_195, 1);
x_219 = lean_ctor_get(x_195, 2);
x_220 = lean_ctor_get(x_195, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_195);
x_221 = 1;
x_222 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_222, 0, x_34);
lean_ctor_set(x_222, 1, x_35);
lean_ctor_set(x_222, 2, x_36);
lean_ctor_set(x_222, 3, x_194);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_221);
lean_ctor_set(x_192, 3, x_220);
lean_ctor_set(x_192, 2, x_219);
lean_ctor_set(x_192, 1, x_218);
lean_ctor_set(x_192, 0, x_217);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_221);
x_223 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_223);
return x_2;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_224 = lean_ctor_get(x_192, 1);
x_225 = lean_ctor_get(x_192, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_192);
x_226 = lean_ctor_get(x_195, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_195, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_195, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_195, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_230 = x_195;
} else {
 lean_dec_ref(x_195);
 x_230 = lean_box(0);
}
x_231 = 1;
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(1, 4, 1);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_34);
lean_ctor_set(x_232, 1, x_35);
lean_ctor_set(x_232, 2, x_36);
lean_ctor_set(x_232, 3, x_194);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
x_233 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_229);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_231);
x_234 = 0;
lean_ctor_set(x_2, 3, x_233);
lean_ctor_set(x_2, 2, x_225);
lean_ctor_set(x_2, 1, x_224);
lean_ctor_set(x_2, 0, x_232);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_234);
return x_2;
}
}
else
{
uint8_t x_235; 
lean_free_object(x_2);
x_235 = !lean_is_exclusive(x_195);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_195, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_195, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_195, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_195, 0);
lean_dec(x_239);
x_240 = 1;
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_240);
return x_195;
}
else
{
uint8_t x_241; lean_object* x_242; 
lean_dec(x_195);
x_241 = 1;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_34);
lean_ctor_set(x_242, 1, x_35);
lean_ctor_set(x_242, 2, x_36);
lean_ctor_set(x_242, 3, x_192);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
return x_242;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_192);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_192, 0);
lean_dec(x_245);
x_246 = !lean_is_exclusive(x_194);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_194, 0);
x_248 = lean_ctor_get(x_194, 1);
x_249 = lean_ctor_get(x_194, 2);
x_250 = lean_ctor_get(x_194, 3);
x_251 = 1;
lean_ctor_set(x_194, 3, x_247);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_251);
lean_ctor_set(x_192, 0, x_250);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_249);
lean_ctor_set(x_2, 1, x_248);
lean_ctor_set(x_2, 0, x_194);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_252);
return x_2;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_194, 0);
x_254 = lean_ctor_get(x_194, 1);
x_255 = lean_ctor_get(x_194, 2);
x_256 = lean_ctor_get(x_194, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_194);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_34);
lean_ctor_set(x_258, 1, x_35);
lean_ctor_set(x_258, 2, x_36);
lean_ctor_set(x_258, 3, x_253);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_192, 0, x_256);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_255);
lean_ctor_set(x_2, 1, x_254);
lean_ctor_set(x_2, 0, x_258);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_259);
return x_2;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_192, 1);
x_261 = lean_ctor_get(x_192, 2);
x_262 = lean_ctor_get(x_192, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_192);
x_263 = lean_ctor_get(x_194, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_194, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_194, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_194, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_267 = x_194;
} else {
 lean_dec_ref(x_194);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_34);
lean_ctor_set(x_269, 1, x_35);
lean_ctor_set(x_269, 2, x_36);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_260);
lean_ctor_set(x_270, 2, x_261);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_2, 3, x_270);
lean_ctor_set(x_2, 2, x_265);
lean_ctor_set(x_2, 1, x_264);
lean_ctor_set(x_2, 0, x_269);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_271);
return x_2;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_192, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_2);
x_273 = !lean_is_exclusive(x_194);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_194, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_194, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_194, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_194, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_194, 3, x_192);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_278);
return x_194;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_194);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_34);
lean_ctor_set(x_280, 1, x_35);
lean_ctor_set(x_280, 2, x_36);
lean_ctor_set(x_280, 3, x_192);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_2);
x_282 = !lean_is_exclusive(x_192);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_192, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_192, 0);
lean_dec(x_284);
x_285 = !lean_is_exclusive(x_272);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_291; 
x_286 = lean_ctor_get(x_272, 0);
x_287 = lean_ctor_get(x_272, 1);
x_288 = lean_ctor_get(x_272, 2);
x_289 = lean_ctor_get(x_272, 3);
x_290 = 1;
lean_inc(x_194);
lean_ctor_set(x_272, 3, x_194);
lean_ctor_set(x_272, 2, x_36);
lean_ctor_set(x_272, 1, x_35);
lean_ctor_set(x_272, 0, x_34);
x_291 = !lean_is_exclusive(x_194);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_292 = lean_ctor_get(x_194, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_194, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_194, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_194, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
lean_ctor_set(x_194, 3, x_289);
lean_ctor_set(x_194, 2, x_288);
lean_ctor_set(x_194, 1, x_287);
lean_ctor_set(x_194, 0, x_286);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_290);
x_296 = 0;
lean_ctor_set(x_192, 3, x_194);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_296);
return x_192;
}
else
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_194);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_287);
lean_ctor_set(x_297, 2, x_288);
lean_ctor_set(x_297, 3, x_289);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_290);
x_298 = 0;
lean_ctor_set(x_192, 3, x_297);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_298);
return x_192;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_ctor_get(x_272, 0);
x_300 = lean_ctor_get(x_272, 1);
x_301 = lean_ctor_get(x_272, 2);
x_302 = lean_ctor_get(x_272, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_272);
x_303 = 1;
lean_inc(x_194);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_34);
lean_ctor_set(x_304, 1, x_35);
lean_ctor_set(x_304, 2, x_36);
lean_ctor_set(x_304, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_305 = x_194;
} else {
 lean_dec_ref(x_194);
 x_305 = lean_box(0);
}
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_303);
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 4, 1);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_299);
lean_ctor_set(x_306, 1, x_300);
lean_ctor_set(x_306, 2, x_301);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_303);
x_307 = 0;
lean_ctor_set(x_192, 3, x_306);
lean_ctor_set(x_192, 0, x_304);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_307);
return x_192;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; 
x_308 = lean_ctor_get(x_192, 1);
x_309 = lean_ctor_get(x_192, 2);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_192);
x_310 = lean_ctor_get(x_272, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_272, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_272, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 3);
lean_inc(x_313);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_314 = x_272;
} else {
 lean_dec_ref(x_272);
 x_314 = lean_box(0);
}
x_315 = 1;
lean_inc(x_194);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(1, 4, 1);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_34);
lean_ctor_set(x_316, 1, x_35);
lean_ctor_set(x_316, 2, x_36);
lean_ctor_set(x_316, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_317 = x_194;
} else {
 lean_dec_ref(x_194);
 x_317 = lean_box(0);
}
lean_ctor_set_uint8(x_316, sizeof(void*)*4, x_315);
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_310);
lean_ctor_set(x_318, 1, x_311);
lean_ctor_set(x_318, 2, x_312);
lean_ctor_set(x_318, 3, x_313);
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_315);
x_319 = 0;
x_320 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_308);
lean_ctor_set(x_320, 2, x_309);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_319);
return x_320;
}
}
else
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_192);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_192, 3);
lean_dec(x_322);
x_323 = lean_ctor_get(x_192, 0);
lean_dec(x_323);
x_324 = !lean_is_exclusive(x_194);
if (x_324 == 0)
{
uint8_t x_325; 
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_281);
x_325 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_325);
return x_2;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_326 = lean_ctor_get(x_194, 0);
x_327 = lean_ctor_get(x_194, 1);
x_328 = lean_ctor_get(x_194, 2);
x_329 = lean_ctor_get(x_194, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_194);
x_330 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_328);
lean_ctor_set(x_330, 3, x_329);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_281);
lean_ctor_set(x_192, 0, x_330);
x_331 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_331);
return x_2;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_332 = lean_ctor_get(x_192, 1);
x_333 = lean_ctor_get(x_192, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_192);
x_334 = lean_ctor_get(x_194, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_194, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_194, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_194, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_338 = x_194;
} else {
 lean_dec_ref(x_194);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 4, 1);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_334);
lean_ctor_set(x_339, 1, x_335);
lean_ctor_set(x_339, 2, x_336);
lean_ctor_set(x_339, 3, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_281);
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
lean_ctor_set(x_340, 2, x_333);
lean_ctor_set(x_340, 3, x_272);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_193);
x_341 = 1;
lean_ctor_set(x_2, 3, x_340);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_341);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_342; 
x_342 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_342);
return x_2;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_343 = lean_ctor_get(x_2, 0);
x_344 = lean_ctor_get(x_2, 1);
x_345 = lean_ctor_get(x_2, 2);
x_346 = lean_ctor_get(x_2, 3);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_2);
x_347 = l_Lean_Name_quickCmp(x_3, x_344);
switch (x_347) {
case 0:
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_343, x_3, x_4);
x_349 = lean_ctor_get_uint8(x_348, sizeof(void*)*4);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_348, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; 
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_354 = x_348;
} else {
 lean_dec_ref(x_348);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 4, 1);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_353);
lean_ctor_set(x_355, 3, x_351);
lean_ctor_set_uint8(x_355, sizeof(void*)*4, x_349);
x_356 = 1;
x_357 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_344);
lean_ctor_set(x_357, 2, x_345);
lean_ctor_set(x_357, 3, x_346);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_356);
return x_357;
}
else
{
uint8_t x_358; 
x_358 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; 
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_361 = x_348;
} else {
 lean_dec_ref(x_348);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_351, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 3);
lean_inc(x_365);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_366 = x_351;
} else {
 lean_dec_ref(x_351);
 x_366 = lean_box(0);
}
x_367 = 1;
if (lean_is_scalar(x_366)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_366;
}
lean_ctor_set(x_368, 0, x_350);
lean_ctor_set(x_368, 1, x_359);
lean_ctor_set(x_368, 2, x_360);
lean_ctor_set(x_368, 3, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_361)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_361;
}
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_344);
lean_ctor_set(x_369, 2, x_345);
lean_ctor_set(x_369, 3, x_346);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_367);
x_370 = 0;
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_363);
lean_ctor_set(x_371, 2, x_364);
lean_ctor_set(x_371, 3, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
return x_371;
}
else
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_372 = x_351;
} else {
 lean_dec_ref(x_351);
 x_372 = lean_box(0);
}
x_373 = 1;
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_348);
lean_ctor_set(x_374, 1, x_344);
lean_ctor_set(x_374, 2, x_345);
lean_ctor_set(x_374, 3, x_346);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; 
x_376 = lean_ctor_get(x_348, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_348, 2);
lean_inc(x_377);
x_378 = lean_ctor_get(x_348, 3);
lean_inc(x_378);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_379 = x_348;
} else {
 lean_dec_ref(x_348);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_350, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_350, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_350, 2);
lean_inc(x_382);
x_383 = lean_ctor_get(x_350, 3);
lean_inc(x_383);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_384 = x_350;
} else {
 lean_dec_ref(x_350);
 x_384 = lean_box(0);
}
x_385 = 1;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_381);
lean_ctor_set(x_386, 2, x_382);
lean_ctor_set(x_386, 3, x_383);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
if (lean_is_scalar(x_379)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_379;
}
lean_ctor_set(x_387, 0, x_378);
lean_ctor_set(x_387, 1, x_344);
lean_ctor_set(x_387, 2, x_345);
lean_ctor_set(x_387, 3, x_346);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_385);
x_388 = 0;
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_376);
lean_ctor_set(x_389, 2, x_377);
lean_ctor_set(x_389, 3, x_387);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
return x_389;
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_348, 3);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_391 = x_350;
} else {
 lean_dec_ref(x_350);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_348);
lean_ctor_set(x_393, 1, x_344);
lean_ctor_set(x_393, 2, x_345);
lean_ctor_set(x_393, 3, x_346);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
return x_393;
}
else
{
uint8_t x_394; 
x_394 = lean_ctor_get_uint8(x_390, sizeof(void*)*4);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_348, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_348, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_397 = x_348;
} else {
 lean_dec_ref(x_348);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_390, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_390, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_390, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_390, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 x_402 = x_390;
} else {
 lean_dec_ref(x_390);
 x_402 = lean_box(0);
}
x_403 = 1;
lean_inc(x_350);
if (lean_is_scalar(x_402)) {
 x_404 = lean_alloc_ctor(1, 4, 1);
} else {
 x_404 = x_402;
}
lean_ctor_set(x_404, 0, x_350);
lean_ctor_set(x_404, 1, x_395);
lean_ctor_set(x_404, 2, x_396);
lean_ctor_set(x_404, 3, x_398);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_405 = x_350;
} else {
 lean_dec_ref(x_350);
 x_405 = lean_box(0);
}
lean_ctor_set_uint8(x_404, sizeof(void*)*4, x_403);
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 4, 1);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_401);
lean_ctor_set(x_406, 1, x_344);
lean_ctor_set(x_406, 2, x_345);
lean_ctor_set(x_406, 3, x_346);
lean_ctor_set_uint8(x_406, sizeof(void*)*4, x_403);
x_407 = 0;
if (lean_is_scalar(x_397)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_397;
}
lean_ctor_set(x_408, 0, x_404);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_408, 2, x_400);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_409 = lean_ctor_get(x_348, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_348, 2);
lean_inc(x_410);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_411 = x_348;
} else {
 lean_dec_ref(x_348);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_350, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_350, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_350, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_350, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_416 = x_350;
} else {
 lean_dec_ref(x_350);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_413);
lean_ctor_set(x_417, 2, x_414);
lean_ctor_set(x_417, 3, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_411)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_411;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_409);
lean_ctor_set(x_418, 2, x_410);
lean_ctor_set(x_418, 3, x_390);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_349);
x_419 = 1;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_344);
lean_ctor_set(x_420, 2, x_345);
lean_ctor_set(x_420, 3, x_346);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
}
}
}
}
else
{
uint8_t x_421; lean_object* x_422; 
x_421 = 1;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_348);
lean_ctor_set(x_422, 1, x_344);
lean_ctor_set(x_422, 2, x_345);
lean_ctor_set(x_422, 3, x_346);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
}
case 1:
{
uint8_t x_423; lean_object* x_424; 
lean_dec(x_345);
lean_dec(x_344);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_343);
lean_ctor_set(x_424, 1, x_3);
lean_ctor_set(x_424, 2, x_4);
lean_ctor_set(x_424, 3, x_346);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
default: 
{
lean_object* x_425; uint8_t x_426; 
x_425 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_346, x_3, x_4);
x_426 = lean_ctor_get_uint8(x_425, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_425, 3);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; 
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_425, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_431 = x_425;
} else {
 lean_dec_ref(x_425);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 4, 1);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_430);
lean_ctor_set(x_432, 3, x_428);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_426);
x_433 = 1;
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_343);
lean_ctor_set(x_434, 1, x_344);
lean_ctor_set(x_434, 2, x_345);
lean_ctor_set(x_434, 3, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_433);
return x_434;
}
else
{
uint8_t x_435; 
x_435 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; 
x_436 = lean_ctor_get(x_425, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_425, 2);
lean_inc(x_437);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_438 = x_425;
} else {
 lean_dec_ref(x_425);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_428, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_428, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_428, 3);
lean_inc(x_442);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_443 = x_428;
} else {
 lean_dec_ref(x_428);
 x_443 = lean_box(0);
}
x_444 = 1;
if (lean_is_scalar(x_443)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_443;
}
lean_ctor_set(x_445, 0, x_343);
lean_ctor_set(x_445, 1, x_344);
lean_ctor_set(x_445, 2, x_345);
lean_ctor_set(x_445, 3, x_427);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_438)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_438;
}
lean_ctor_set(x_446, 0, x_439);
lean_ctor_set(x_446, 1, x_440);
lean_ctor_set(x_446, 2, x_441);
lean_ctor_set(x_446, 3, x_442);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_444);
x_447 = 0;
x_448 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_436);
lean_ctor_set(x_448, 2, x_437);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
return x_448;
}
else
{
lean_object* x_449; uint8_t x_450; lean_object* x_451; 
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_449 = x_428;
} else {
 lean_dec_ref(x_428);
 x_449 = lean_box(0);
}
x_450 = 1;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_343);
lean_ctor_set(x_451, 1, x_344);
lean_ctor_set(x_451, 2, x_345);
lean_ctor_set(x_451, 3, x_425);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
x_452 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; 
x_453 = lean_ctor_get(x_425, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_425, 2);
lean_inc(x_454);
x_455 = lean_ctor_get(x_425, 3);
lean_inc(x_455);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_456 = x_425;
} else {
 lean_dec_ref(x_425);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_427, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_427, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_427, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_427, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_461 = x_427;
} else {
 lean_dec_ref(x_427);
 x_461 = lean_box(0);
}
x_462 = 1;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_343);
lean_ctor_set(x_463, 1, x_344);
lean_ctor_set(x_463, 2, x_345);
lean_ctor_set(x_463, 3, x_457);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
if (lean_is_scalar(x_456)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_456;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_453);
lean_ctor_set(x_464, 2, x_454);
lean_ctor_set(x_464, 3, x_455);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_462);
x_465 = 0;
x_466 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_458);
lean_ctor_set(x_466, 2, x_459);
lean_ctor_set(x_466, 3, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
return x_466;
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_425, 3);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; uint8_t x_469; lean_object* x_470; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_468 = x_427;
} else {
 lean_dec_ref(x_427);
 x_468 = lean_box(0);
}
x_469 = 1;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_343);
lean_ctor_set(x_470, 1, x_344);
lean_ctor_set(x_470, 2, x_345);
lean_ctor_set(x_470, 3, x_425);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
return x_470;
}
else
{
uint8_t x_471; 
x_471 = lean_ctor_get_uint8(x_467, sizeof(void*)*4);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; 
x_472 = lean_ctor_get(x_425, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_425, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_474 = x_425;
} else {
 lean_dec_ref(x_425);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_467, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_467, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_467, 2);
lean_inc(x_477);
x_478 = lean_ctor_get(x_467, 3);
lean_inc(x_478);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 x_479 = x_467;
} else {
 lean_dec_ref(x_467);
 x_479 = lean_box(0);
}
x_480 = 1;
lean_inc(x_427);
if (lean_is_scalar(x_479)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_479;
}
lean_ctor_set(x_481, 0, x_343);
lean_ctor_set(x_481, 1, x_344);
lean_ctor_set(x_481, 2, x_345);
lean_ctor_set(x_481, 3, x_427);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_482 = x_427;
} else {
 lean_dec_ref(x_427);
 x_482 = lean_box(0);
}
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_480);
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_475);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_478);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_480);
x_484 = 0;
if (lean_is_scalar(x_474)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_474;
}
lean_ctor_set(x_485, 0, x_481);
lean_ctor_set(x_485, 1, x_472);
lean_ctor_set(x_485, 2, x_473);
lean_ctor_set(x_485, 3, x_483);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; 
x_486 = lean_ctor_get(x_425, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_425, 2);
lean_inc(x_487);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_488 = x_425;
} else {
 lean_dec_ref(x_425);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_427, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_427, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_427, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_427, 3);
lean_inc(x_492);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_493 = x_427;
} else {
 lean_dec_ref(x_427);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_490);
lean_ctor_set(x_494, 2, x_491);
lean_ctor_set(x_494, 3, x_492);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_488)) {
 x_495 = lean_alloc_ctor(1, 4, 1);
} else {
 x_495 = x_488;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_486);
lean_ctor_set(x_495, 2, x_487);
lean_ctor_set(x_495, 3, x_467);
lean_ctor_set_uint8(x_495, sizeof(void*)*4, x_426);
x_496 = 1;
x_497 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_497, 0, x_343);
lean_ctor_set(x_497, 1, x_344);
lean_ctor_set(x_497, 2, x_345);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
return x_497;
}
}
}
}
}
else
{
uint8_t x_498; lean_object* x_499; 
x_498 = 1;
x_499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_499, 0, x_343);
lean_ctor_set(x_499, 1, x_344);
lean_ctor_set(x_499, 2, x_345);
lean_ctor_set(x_499, 3, x_425);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_498);
return x_499;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_loadLeanConfig___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = l_Lean_RBNode_insert___at_Lake_loadLeanConfig___spec__1(x_1, x_5, x_8, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_loadLeanConfig___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_loadLeanConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_loadLeanConfig___closed__2;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Lake_loadLeanConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_loadLeanConfig___closed__2;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_loadLeanConfig___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_loadLeanConfig___closed__2;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lake_importConfigFile(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_191; lean_object* x_192; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_1, 7);
lean_inc(x_11);
lean_inc(x_9);
x_191 = l_Lake_PackageDecl_loadFromEnv(x_9, x_11);
x_192 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__5(x_191, x_6);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_ctor_set(x_5, 0, x_193);
x_12 = x_5;
x_13 = x_194;
goto block_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_dec(x_192);
x_197 = lean_io_error_to_string(x_195);
x_198 = 3;
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
x_200 = lean_array_get_size(x_10);
x_201 = lean_array_push(x_10, x_199);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_201);
lean_ctor_set(x_5, 0, x_200);
x_12 = x_5;
x_13 = x_196;
goto block_190;
}
block_190:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = l_System_FilePath_join(x_19, x_20);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 8);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 9);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_ctor_get(x_17, 16);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 18);
lean_inc(x_28);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_107; 
x_107 = l_Lake_loadLeanConfig___closed__3;
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_18);
x_108 = l_Lake_defaultManifestFile;
x_109 = l_Lake_loadLeanConfig___closed__1;
x_110 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_110, 0, x_16);
lean_ctor_set(x_110, 1, x_21);
lean_ctor_set(x_110, 2, x_20);
lean_ctor_set(x_110, 3, x_17);
lean_ctor_set(x_110, 4, x_22);
lean_ctor_set(x_110, 5, x_108);
lean_ctor_set(x_110, 6, x_24);
lean_ctor_set(x_110, 7, x_25);
lean_ctor_set(x_110, 8, x_109);
lean_ctor_set(x_110, 9, x_109);
lean_ctor_set(x_110, 10, x_26);
lean_ctor_set(x_110, 11, x_109);
lean_ctor_set(x_110, 12, x_26);
lean_ctor_set(x_110, 13, x_109);
lean_ctor_set(x_110, 14, x_109);
lean_ctor_set(x_110, 15, x_27);
lean_ctor_set(x_110, 16, x_28);
lean_inc(x_9);
x_111 = l_Lake_Package_loadFromEnv(x_110, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_9);
lean_ctor_set(x_112, 0, x_117);
return x_111;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_112, 0);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_112);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_9);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_111, 0, x_121);
return x_111;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_111, 1);
lean_inc(x_122);
lean_dec(x_111);
x_123 = lean_ctor_get(x_112, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_125 = x_112;
} else {
 lean_dec_ref(x_112);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_9);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_122);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec(x_9);
x_129 = !lean_is_exclusive(x_111);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_111, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_112);
if (x_131 == 0)
{
return x_111;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_112, 0);
x_133 = lean_ctor_get(x_112, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_112);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_111, 0, x_134);
return x_111;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_111, 1);
lean_inc(x_135);
lean_dec(x_111);
x_136 = lean_ctor_get(x_112, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_112, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_138 = x_112;
} else {
 lean_dec_ref(x_112);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_9);
x_141 = !lean_is_exclusive(x_111);
if (x_141 == 0)
{
return x_111;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_111, 0);
x_143 = lean_ctor_get(x_111, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_111);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; 
x_145 = l_Lake_defaultManifestFile;
x_29 = x_145;
goto block_106;
}
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_23, 0);
lean_inc(x_146);
lean_dec(x_23);
x_147 = l_Lake_loadLeanConfig___closed__3;
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_18);
x_148 = l_Lake_loadLeanConfig___closed__1;
x_149 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_149, 0, x_16);
lean_ctor_set(x_149, 1, x_21);
lean_ctor_set(x_149, 2, x_20);
lean_ctor_set(x_149, 3, x_17);
lean_ctor_set(x_149, 4, x_22);
lean_ctor_set(x_149, 5, x_146);
lean_ctor_set(x_149, 6, x_24);
lean_ctor_set(x_149, 7, x_25);
lean_ctor_set(x_149, 8, x_148);
lean_ctor_set(x_149, 9, x_148);
lean_ctor_set(x_149, 10, x_26);
lean_ctor_set(x_149, 11, x_148);
lean_ctor_set(x_149, 12, x_26);
lean_ctor_set(x_149, 13, x_148);
lean_ctor_set(x_149, 14, x_148);
lean_ctor_set(x_149, 15, x_27);
lean_ctor_set(x_149, 16, x_28);
lean_inc(x_9);
x_150 = l_Lake_Package_loadFromEnv(x_149, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_150, 0);
lean_dec(x_153);
x_154 = !lean_is_exclusive(x_151);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_151, 0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_9);
lean_ctor_set(x_151, 0, x_156);
return x_150;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_151, 0);
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_151);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_9);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_150, 0, x_160);
return x_150;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_150, 1);
lean_inc(x_161);
lean_dec(x_150);
x_162 = lean_ctor_get(x_151, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_151, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_164 = x_151;
} else {
 lean_dec_ref(x_151);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_9);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
}
else
{
uint8_t x_168; 
lean_dec(x_9);
x_168 = !lean_is_exclusive(x_150);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_150, 0);
lean_dec(x_169);
x_170 = !lean_is_exclusive(x_151);
if (x_170 == 0)
{
return x_150;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_151, 0);
x_172 = lean_ctor_get(x_151, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_151);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_150, 0, x_173);
return x_150;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_150, 1);
lean_inc(x_174);
lean_dec(x_150);
x_175 = lean_ctor_get(x_151, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_151, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_177 = x_151;
} else {
 lean_dec_ref(x_151);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_174);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_9);
x_180 = !lean_is_exclusive(x_150);
if (x_180 == 0)
{
return x_150;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_150, 0);
x_182 = lean_ctor_get(x_150, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_150);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
x_29 = x_146;
goto block_106;
}
}
block_106:
{
uint8_t x_30; 
x_30 = l_Lake_loadLeanConfig___closed__4;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lake_loadLeanConfig___closed__1;
x_32 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_17);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_24);
lean_ctor_set(x_32, 7, x_25);
lean_ctor_set(x_32, 8, x_31);
lean_ctor_set(x_32, 9, x_31);
lean_ctor_set(x_32, 10, x_26);
lean_ctor_set(x_32, 11, x_31);
lean_ctor_set(x_32, 12, x_26);
lean_ctor_set(x_32, 13, x_31);
lean_ctor_set(x_32, 14, x_31);
lean_ctor_set(x_32, 15, x_27);
lean_ctor_set(x_32, 16, x_28);
lean_inc(x_9);
x_33 = l_Lake_Package_loadFromEnv(x_32, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
if (lean_is_scalar(x_18)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_18;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
lean_ctor_set(x_34, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
if (lean_is_scalar(x_18)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_18;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_33, 0, x_43);
return x_33;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_47 = x_34;
} else {
 lean_dec_ref(x_34);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_18;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_9);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_33, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_33, 0, x_56);
return x_33;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
lean_dec(x_33);
x_58 = lean_ctor_get(x_34, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_60 = x_34;
} else {
 lean_dec_ref(x_34);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_18);
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_33);
if (x_63 == 0)
{
return x_33;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_33, 0);
x_65 = lean_ctor_get(x_33, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_33);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
size_t x_67; lean_object* x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = 0;
x_68 = l_Lake_loadLeanConfig___closed__1;
x_69 = l_Lake_loadLeanConfig___closed__5;
x_70 = l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4(x_16, x_68, x_67, x_69, x_26);
x_71 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_71, 0, x_16);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_20);
lean_ctor_set(x_71, 3, x_17);
lean_ctor_set(x_71, 4, x_22);
lean_ctor_set(x_71, 5, x_29);
lean_ctor_set(x_71, 6, x_24);
lean_ctor_set(x_71, 7, x_25);
lean_ctor_set(x_71, 8, x_68);
lean_ctor_set(x_71, 9, x_68);
lean_ctor_set(x_71, 10, x_70);
lean_ctor_set(x_71, 11, x_68);
lean_ctor_set(x_71, 12, x_26);
lean_ctor_set(x_71, 13, x_68);
lean_ctor_set(x_71, 14, x_68);
lean_ctor_set(x_71, 15, x_27);
lean_ctor_set(x_71, 16, x_28);
lean_inc(x_9);
x_72 = l_Lake_Package_loadFromEnv(x_71, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_73, 0);
if (lean_is_scalar(x_18)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_18;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_9);
lean_ctor_set(x_73, 0, x_78);
return x_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
if (lean_is_scalar(x_18)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_18;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_9);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_72, 0, x_82);
return x_72;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_86 = x_73;
} else {
 lean_dec_ref(x_73);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_18;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_9);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_18);
lean_dec(x_9);
x_90 = !lean_is_exclusive(x_72);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_72, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_73);
if (x_92 == 0)
{
return x_72;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_73, 0);
x_94 = lean_ctor_get(x_73, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_73);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_72, 0, x_95);
return x_72;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_72, 1);
lean_inc(x_96);
lean_dec(x_72);
x_97 = lean_ctor_get(x_73, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_73, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_99 = x_73;
} else {
 lean_dec_ref(x_73);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_18);
lean_dec(x_9);
x_102 = !lean_is_exclusive(x_72);
if (x_102 == 0)
{
return x_72;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_72, 0);
x_104 = lean_ctor_get(x_72, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_72);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_12);
if (x_184 == 0)
{
lean_object* x_185; 
if (lean_is_scalar(x_7)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_7;
}
lean_ctor_set(x_185, 0, x_12);
lean_ctor_set(x_185, 1, x_13);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_12, 0);
x_187 = lean_ctor_get(x_12, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_12);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
if (lean_is_scalar(x_7)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_7;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_13);
return x_189;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_331; lean_object* x_332; 
x_202 = lean_ctor_get(x_5, 0);
x_203 = lean_ctor_get(x_5, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_5);
x_204 = lean_ctor_get(x_1, 7);
lean_inc(x_204);
lean_inc(x_202);
x_331 = l_Lake_PackageDecl_loadFromEnv(x_202, x_204);
x_332 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__5(x_331, x_6);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_203);
x_205 = x_335;
x_206 = x_334;
goto block_330;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_336 = lean_ctor_get(x_332, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_332, 1);
lean_inc(x_337);
lean_dec(x_332);
x_338 = lean_io_error_to_string(x_336);
x_339 = 3;
x_340 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*1, x_339);
x_341 = lean_array_get_size(x_203);
x_342 = lean_array_push(x_203, x_340);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_205 = x_343;
x_206 = x_337;
goto block_330;
}
block_330:
{
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_7);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_1, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_1, 3);
lean_inc(x_213);
x_214 = l_System_FilePath_join(x_212, x_213);
x_215 = lean_ctor_get(x_1, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_1, 8);
lean_inc(x_217);
x_218 = lean_ctor_get(x_1, 9);
lean_inc(x_218);
lean_dec(x_1);
x_219 = lean_box(0);
x_220 = lean_ctor_get(x_210, 16);
lean_inc(x_220);
x_221 = lean_ctor_get(x_210, 18);
lean_inc(x_221);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_274; 
x_274 = l_Lake_loadLeanConfig___closed__3;
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_211);
x_275 = l_Lake_defaultManifestFile;
x_276 = l_Lake_loadLeanConfig___closed__1;
x_277 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_277, 0, x_209);
lean_ctor_set(x_277, 1, x_214);
lean_ctor_set(x_277, 2, x_213);
lean_ctor_set(x_277, 3, x_210);
lean_ctor_set(x_277, 4, x_215);
lean_ctor_set(x_277, 5, x_275);
lean_ctor_set(x_277, 6, x_217);
lean_ctor_set(x_277, 7, x_218);
lean_ctor_set(x_277, 8, x_276);
lean_ctor_set(x_277, 9, x_276);
lean_ctor_set(x_277, 10, x_219);
lean_ctor_set(x_277, 11, x_276);
lean_ctor_set(x_277, 12, x_219);
lean_ctor_set(x_277, 13, x_276);
lean_ctor_set(x_277, 14, x_276);
lean_ctor_set(x_277, 15, x_220);
lean_ctor_set(x_277, 16, x_221);
lean_inc(x_202);
x_278 = l_Lake_Package_loadFromEnv(x_277, x_202, x_204, x_208, x_206);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_281 = x_278;
} else {
 lean_dec_ref(x_278);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_279, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_279, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_284 = x_279;
} else {
 lean_dec_ref(x_279);
 x_284 = lean_box(0);
}
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_202);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
if (lean_is_scalar(x_281)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_281;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_280);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_202);
x_288 = lean_ctor_get(x_278, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_289 = x_278;
} else {
 lean_dec_ref(x_278);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_279, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_279, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_292 = x_279;
} else {
 lean_dec_ref(x_279);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
if (lean_is_scalar(x_289)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_289;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_288);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_202);
x_295 = lean_ctor_get(x_278, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_278, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_297 = x_278;
} else {
 lean_dec_ref(x_278);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
else
{
lean_object* x_299; 
x_299 = l_Lake_defaultManifestFile;
x_222 = x_299;
goto block_273;
}
}
else
{
lean_object* x_300; uint8_t x_301; 
x_300 = lean_ctor_get(x_216, 0);
lean_inc(x_300);
lean_dec(x_216);
x_301 = l_Lake_loadLeanConfig___closed__3;
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_211);
x_302 = l_Lake_loadLeanConfig___closed__1;
x_303 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_303, 0, x_209);
lean_ctor_set(x_303, 1, x_214);
lean_ctor_set(x_303, 2, x_213);
lean_ctor_set(x_303, 3, x_210);
lean_ctor_set(x_303, 4, x_215);
lean_ctor_set(x_303, 5, x_300);
lean_ctor_set(x_303, 6, x_217);
lean_ctor_set(x_303, 7, x_218);
lean_ctor_set(x_303, 8, x_302);
lean_ctor_set(x_303, 9, x_302);
lean_ctor_set(x_303, 10, x_219);
lean_ctor_set(x_303, 11, x_302);
lean_ctor_set(x_303, 12, x_219);
lean_ctor_set(x_303, 13, x_302);
lean_ctor_set(x_303, 14, x_302);
lean_ctor_set(x_303, 15, x_220);
lean_ctor_set(x_303, 16, x_221);
lean_inc(x_202);
x_304 = l_Lake_Package_loadFromEnv(x_303, x_202, x_204, x_208, x_206);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_305, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_310 = x_305;
} else {
 lean_dec_ref(x_305);
 x_310 = lean_box(0);
}
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_202);
if (lean_is_scalar(x_310)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_310;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_309);
if (lean_is_scalar(x_307)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_307;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_306);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_202);
x_314 = lean_ctor_get(x_304, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_315 = x_304;
} else {
 lean_dec_ref(x_304);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_305, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_305, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_318 = x_305;
} else {
 lean_dec_ref(x_305);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
if (lean_is_scalar(x_315)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_315;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_314);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_202);
x_321 = lean_ctor_get(x_304, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_304, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_323 = x_304;
} else {
 lean_dec_ref(x_304);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
x_222 = x_300;
goto block_273;
}
}
block_273:
{
uint8_t x_223; 
x_223 = l_Lake_loadLeanConfig___closed__4;
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = l_Lake_loadLeanConfig___closed__1;
x_225 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_225, 0, x_209);
lean_ctor_set(x_225, 1, x_214);
lean_ctor_set(x_225, 2, x_213);
lean_ctor_set(x_225, 3, x_210);
lean_ctor_set(x_225, 4, x_215);
lean_ctor_set(x_225, 5, x_222);
lean_ctor_set(x_225, 6, x_217);
lean_ctor_set(x_225, 7, x_218);
lean_ctor_set(x_225, 8, x_224);
lean_ctor_set(x_225, 9, x_224);
lean_ctor_set(x_225, 10, x_219);
lean_ctor_set(x_225, 11, x_224);
lean_ctor_set(x_225, 12, x_219);
lean_ctor_set(x_225, 13, x_224);
lean_ctor_set(x_225, 14, x_224);
lean_ctor_set(x_225, 15, x_220);
lean_ctor_set(x_225, 16, x_221);
lean_inc(x_202);
x_226 = l_Lake_Package_loadFromEnv(x_225, x_202, x_204, x_208, x_206);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_232 = x_227;
} else {
 lean_dec_ref(x_227);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_211;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_202);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_231);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_229;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_228);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_211);
lean_dec(x_202);
x_236 = lean_ctor_get(x_226, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_237 = x_226;
} else {
 lean_dec_ref(x_226);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_227, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_227, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_240 = x_227;
} else {
 lean_dec_ref(x_227);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_236);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_211);
lean_dec(x_202);
x_243 = lean_ctor_get(x_226, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_226, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_245 = x_226;
} else {
 lean_dec_ref(x_226);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
size_t x_247; lean_object* x_248; size_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = 0;
x_248 = l_Lake_loadLeanConfig___closed__1;
x_249 = l_Lake_loadLeanConfig___closed__5;
x_250 = l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4(x_209, x_248, x_247, x_249, x_219);
x_251 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_251, 0, x_209);
lean_ctor_set(x_251, 1, x_214);
lean_ctor_set(x_251, 2, x_213);
lean_ctor_set(x_251, 3, x_210);
lean_ctor_set(x_251, 4, x_215);
lean_ctor_set(x_251, 5, x_222);
lean_ctor_set(x_251, 6, x_217);
lean_ctor_set(x_251, 7, x_218);
lean_ctor_set(x_251, 8, x_248);
lean_ctor_set(x_251, 9, x_248);
lean_ctor_set(x_251, 10, x_250);
lean_ctor_set(x_251, 11, x_248);
lean_ctor_set(x_251, 12, x_219);
lean_ctor_set(x_251, 13, x_248);
lean_ctor_set(x_251, 14, x_248);
lean_ctor_set(x_251, 15, x_220);
lean_ctor_set(x_251, 16, x_221);
lean_inc(x_202);
x_252 = l_Lake_Package_loadFromEnv(x_251, x_202, x_204, x_208, x_206);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_258 = x_253;
} else {
 lean_dec_ref(x_253);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_211;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_202);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
if (lean_is_scalar(x_255)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_255;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_254);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_211);
lean_dec(x_202);
x_262 = lean_ctor_get(x_252, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_263 = x_252;
} else {
 lean_dec_ref(x_252);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_253, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_253, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_266 = x_253;
} else {
 lean_dec_ref(x_253);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
if (lean_is_scalar(x_263)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_263;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_262);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_211);
lean_dec(x_202);
x_269 = lean_ctor_get(x_252, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_252, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_271 = x_252;
} else {
 lean_dec_ref(x_252);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_1);
x_325 = lean_ctor_get(x_205, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_205, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_327 = x_205;
} else {
 lean_dec_ref(x_205);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
if (lean_is_scalar(x_7)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_7;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_206);
return x_329;
}
}
}
}
else
{
uint8_t x_344; 
lean_dec(x_1);
x_344 = !lean_is_exclusive(x_4);
if (x_344 == 0)
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_4, 0);
lean_dec(x_345);
x_346 = !lean_is_exclusive(x_5);
if (x_346 == 0)
{
return x_4;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_5, 0);
x_348 = lean_ctor_get(x_5, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_5);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
lean_ctor_set(x_4, 0, x_349);
return x_4;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_350 = lean_ctor_get(x_4, 1);
lean_inc(x_350);
lean_dec(x_4);
x_351 = lean_ctor_get(x_5, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_5, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_353 = x_5;
} else {
 lean_dec_ref(x_5);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_350);
return x_355;
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_1);
x_356 = !lean_is_exclusive(x_4);
if (x_356 == 0)
{
return x_4;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_4, 0);
x_358 = lean_ctor_get(x_4, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_4);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_loadLeanConfig___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_loadLeanConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at_Lake_loadLeanConfig___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_loadLeanConfig___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lake_loadLeanConfig___closed__4 = _init_l_Lake_loadLeanConfig___closed__4();
l_Lake_loadLeanConfig___closed__5 = _init_l_Lake_loadLeanConfig___closed__5();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
