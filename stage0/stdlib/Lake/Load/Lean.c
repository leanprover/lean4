// Lean compiler output
// Module: Lake.Load.Lean
// Imports: public import Lean.Environment public import Lake.Config.Package public import Lake.Load.Config import Lake.Load.Lean.Elab import Lake.Load.Lean.Eval
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lake_loadLeanConfig___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static size_t l_Lake_loadLeanConfig___closed__7;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_loadLeanConfig___closed__6;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_PackageDecl_loadFromEnv(lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__8;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__4;
static uint8_t l_Lake_loadLeanConfig___closed__5;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
static lean_object* l_Lake_loadLeanConfig___closed__0;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_mk_io_user_error(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(x_1, x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_22);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_26);
x_34 = lean_nat_dec_lt(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_45; lean_object* x_46; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
x_36 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_37 = lean_nat_add(x_36, x_13);
lean_dec(x_36);
x_45 = lean_nat_add(x_12, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_nat_add(x_38, x_40);
lean_dec(x_40);
lean_dec(x_38);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_6);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set(x_42, 4, x_8);
if (lean_is_scalar(x_25)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_25;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_39);
lean_ctor_set(x_43, 4, x_42);
return x_43;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_16);
lean_ctor_set(x_48, 3, x_17);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_38 = x_49;
x_39 = x_48;
x_40 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_38 = x_49;
x_39 = x_48;
x_40 = x_51;
goto block_44;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_9);
x_55 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_56 = lean_nat_add(x_55, x_13);
lean_dec(x_55);
x_57 = lean_nat_add(x_12, x_13);
x_58 = lean_nat_add(x_57, x_27);
lean_dec(x_57);
lean_inc_ref(x_8);
if (lean_is_scalar(x_25)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_25;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_6);
lean_ctor_set(x_59, 3, x_18);
lean_ctor_set(x_59, 4, x_8);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_8, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_8, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_8, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_8, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_8, 0);
lean_dec(x_65);
lean_ctor_set(x_8, 4, x_59);
lean_ctor_set(x_8, 3, x_17);
lean_ctor_set(x_8, 2, x_16);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_56);
return x_8;
}
else
{
lean_object* x_66; 
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_15);
lean_ctor_set(x_66, 2, x_16);
lean_ctor_set(x_66, 3, x_17);
lean_ctor_set(x_66, 4, x_59);
return x_66;
}
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_11, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_11, 4);
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get(x_11, 2);
x_72 = lean_ctor_get(x_11, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_11, 0);
lean_dec(x_73);
x_74 = lean_unsigned_to_nat(3u);
lean_inc(x_69);
lean_ctor_set(x_11, 3, x_69);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_11);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_11, 4);
x_77 = lean_ctor_get(x_11, 1);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_76);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_unsigned_to_nat(3u);
lean_inc(x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_5);
lean_ctor_set(x_80, 2, x_6);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_9;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_67);
lean_ctor_set(x_81, 4, x_80);
return x_81;
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_11, 4);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_11, 1);
x_85 = lean_ctor_get(x_11, 2);
x_86 = lean_ctor_get(x_11, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_11, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_11, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_82, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_82, 0);
lean_dec(x_94);
x_95 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_82, 4, x_67);
lean_ctor_set(x_82, 3, x_67);
lean_ctor_set(x_82, 2, x_85);
lean_ctor_set(x_82, 1, x_84);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_9;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_11);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_82, 1);
x_98 = lean_ctor_get(x_82, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_82);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_12);
lean_ctor_set(x_100, 1, x_84);
lean_ctor_set(x_100, 2, x_85);
lean_ctor_set(x_100, 3, x_67);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_9;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_11);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_11, 1);
x_103 = lean_ctor_get(x_11, 2);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
x_104 = lean_ctor_get(x_82, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 2);
lean_inc(x_105);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_106 = x_82;
} else {
 lean_dec_ref(x_82);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_67);
lean_ctor_set(x_108, 4, x_67);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_9;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_5);
lean_ctor_set(x_112, 2, x_6);
lean_ctor_set(x_112, 3, x_11);
lean_ctor_set(x_112, 4, x_82);
return x_112;
}
}
}
}
case 1:
{
lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_1);
lean_ctor_set(x_113, 2, x_2);
lean_ctor_set(x_113, 3, x_7);
lean_ctor_set(x_113, 4, x_8);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_114 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(x_1, x_2, x_8);
x_115 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_7, 0);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 4);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_mul(x_122, x_116);
x_124 = lean_nat_dec_lt(x_123, x_117);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
x_125 = lean_nat_add(x_115, x_116);
x_126 = lean_nat_add(x_125, x_117);
lean_dec(x_117);
lean_dec(x_125);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
lean_ctor_set(x_127, 2, x_6);
lean_ctor_set(x_127, 3, x_7);
lean_ctor_set(x_127, 4, x_114);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_128 = x_114;
} else {
 lean_dec_ref(x_114);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
x_130 = lean_ctor_get(x_120, 1);
x_131 = lean_ctor_get(x_120, 2);
x_132 = lean_ctor_get(x_120, 3);
x_133 = lean_ctor_get(x_120, 4);
x_134 = lean_ctor_get(x_121, 0);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_mul(x_135, x_134);
x_137 = lean_nat_dec_lt(x_129, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_148; 
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_138 = x_120;
} else {
 lean_dec_ref(x_120);
 x_138 = lean_box(0);
}
x_139 = lean_nat_add(x_115, x_116);
x_140 = lean_nat_add(x_139, x_117);
lean_dec(x_117);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_132, 0);
lean_inc(x_155);
x_148 = x_155;
goto block_154;
}
else
{
lean_object* x_156; 
x_156 = lean_unsigned_to_nat(0u);
x_148 = x_156;
goto block_154;
}
block_147:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_nat_add(x_141, x_143);
lean_dec(x_143);
lean_dec(x_141);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_118);
lean_ctor_set(x_145, 2, x_119);
lean_ctor_set(x_145, 3, x_133);
lean_ctor_set(x_145, 4, x_121);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_130);
lean_ctor_set(x_146, 2, x_131);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_145);
return x_146;
}
block_154:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_nat_add(x_139, x_148);
lean_dec(x_148);
lean_dec(x_139);
if (lean_is_scalar(x_9)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_9;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_5);
lean_ctor_set(x_150, 2, x_6);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_132);
x_151 = lean_nat_add(x_115, x_134);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
x_141 = x_151;
x_142 = x_150;
x_143 = x_152;
goto block_147;
}
else
{
lean_object* x_153; 
x_153 = lean_unsigned_to_nat(0u);
x_141 = x_151;
x_142 = x_150;
x_143 = x_153;
goto block_147;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_9);
x_157 = lean_nat_add(x_115, x_116);
x_158 = lean_nat_add(x_157, x_117);
lean_dec(x_117);
x_159 = lean_nat_add(x_157, x_129);
lean_dec(x_157);
lean_inc_ref(x_7);
if (lean_is_scalar(x_128)) {
 x_160 = lean_alloc_ctor(0, 5, 0);
} else {
 x_160 = x_128;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_5);
lean_ctor_set(x_160, 2, x_6);
lean_ctor_set(x_160, 3, x_7);
lean_ctor_set(x_160, 4, x_120);
x_161 = !lean_is_exclusive(x_7);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_7, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_7, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_7, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_7, 0);
lean_dec(x_166);
lean_ctor_set(x_7, 4, x_121);
lean_ctor_set(x_7, 3, x_160);
lean_ctor_set(x_7, 2, x_119);
lean_ctor_set(x_7, 1, x_118);
lean_ctor_set(x_7, 0, x_158);
return x_7;
}
else
{
lean_object* x_167; 
lean_dec(x_7);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_118);
lean_ctor_set(x_167, 2, x_119);
lean_ctor_set(x_167, 3, x_160);
lean_ctor_set(x_167, 4, x_121);
return x_167;
}
}
}
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_114, 3);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_114);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_114, 4);
x_171 = lean_ctor_get(x_114, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_114, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_168);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_168, 1);
x_175 = lean_ctor_get(x_168, 2);
x_176 = lean_ctor_get(x_168, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_168, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_168, 0);
lean_dec(x_178);
x_179 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
lean_ctor_set(x_168, 4, x_170);
lean_ctor_set(x_168, 3, x_170);
lean_ctor_set(x_168, 2, x_6);
lean_ctor_set(x_168, 1, x_5);
lean_ctor_set(x_168, 0, x_115);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_9;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
lean_ctor_set(x_180, 2, x_175);
lean_ctor_set(x_180, 3, x_168);
lean_ctor_set(x_180, 4, x_114);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_168, 1);
x_182 = lean_ctor_get(x_168, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_168);
x_183 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_115);
lean_ctor_set(x_184, 1, x_5);
lean_ctor_set(x_184, 2, x_6);
lean_ctor_set(x_184, 3, x_170);
lean_ctor_set(x_184, 4, x_170);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_9;
}
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_185, 4, x_114);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_114, 4);
x_187 = lean_ctor_get(x_114, 1);
x_188 = lean_ctor_get(x_114, 2);
lean_inc(x_186);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_114);
x_189 = lean_ctor_get(x_168, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_168, 2);
lean_inc(x_190);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_191 = x_168;
} else {
 lean_dec_ref(x_168);
 x_191 = lean_box(0);
}
x_192 = lean_unsigned_to_nat(3u);
lean_inc_n(x_186, 2);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_115);
lean_ctor_set(x_193, 1, x_5);
lean_ctor_set(x_193, 2, x_6);
lean_ctor_set(x_193, 3, x_186);
lean_ctor_set(x_193, 4, x_186);
lean_inc(x_186);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_115);
lean_ctor_set(x_194, 1, x_187);
lean_ctor_set(x_194, 2, x_188);
lean_ctor_set(x_194, 3, x_186);
lean_ctor_set(x_194, 4, x_186);
if (lean_is_scalar(x_9)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_9;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_190);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_194);
return x_195;
}
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_114, 4);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_114);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_114, 1);
x_199 = lean_ctor_get(x_114, 2);
x_200 = lean_ctor_get(x_114, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_114, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_114, 0);
lean_dec(x_202);
x_203 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_114, 4, x_168);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_9;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_114);
lean_ctor_set(x_204, 4, x_196);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_114, 1);
x_206 = lean_ctor_get(x_114, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_115);
lean_ctor_set(x_208, 1, x_5);
lean_ctor_set(x_208, 2, x_6);
lean_ctor_set(x_208, 3, x_168);
lean_ctor_set(x_208, 4, x_168);
if (lean_is_scalar(x_9)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_9;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_205);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_208);
lean_ctor_set(x_209, 4, x_196);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_9;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_5);
lean_ctor_set(x_211, 2, x_6);
lean_ctor_set(x_211, 3, x_196);
lean_ctor_set(x_211, 4, x_114);
return x_211;
}
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_1);
lean_ctor_set(x_213, 2, x_2);
lean_ctor_set(x_213, 3, x_3);
lean_ctor_set(x_213, 4, x_3);
return x_213;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(x_7, x_6, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_loadLeanConfig_spec__1___redArg(x_8, x_7, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg(x_2, x_11, x_4, x_9);
return x_12;
}
else
{
return x_5;
}
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_System_Platform_target;
return x_1;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".tar.gz", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_loadLeanConfig___closed__3;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_loadLeanConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_loadLeanConfig___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_loadLeanConfig___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_loadLeanConfig___closed__4;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_loadLeanConfig___closed__7() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_loadLeanConfig___closed__4;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultManifestFile;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_4 = l_Lake_importConfigFile(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 10);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
lean_inc(x_10);
x_19 = l_Lake_PackageDecl_loadFromEnv(x_10, x_16);
x_20 = l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(x_19, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_90; 
lean_free_object(x_5);
lean_free_object(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 2);
x_28 = lean_ctor_get(x_22, 12);
x_29 = lean_ctor_get(x_22, 13);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_22, 15);
lean_inc_ref(x_30);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_101; 
x_101 = l_Lake_loadLeanConfig___closed__8;
x_90 = x_101;
goto block_100;
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_27, 0);
lean_inc(x_102);
x_90 = x_102;
goto block_100;
}
block_72:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_26);
lean_ctor_set(x_41, 2, x_13);
lean_ctor_set(x_41, 3, x_12);
lean_ctor_set(x_41, 4, x_22);
lean_ctor_set(x_41, 5, x_15);
lean_ctor_set(x_41, 6, x_14);
lean_ctor_set(x_41, 7, x_33);
lean_ctor_set(x_41, 8, x_17);
lean_ctor_set(x_41, 9, x_18);
lean_ctor_set(x_41, 10, x_31);
lean_ctor_set(x_41, 11, x_32);
lean_ctor_set(x_41, 12, x_37);
lean_ctor_set(x_41, 13, x_36);
lean_ctor_set(x_41, 14, x_34);
lean_ctor_set(x_41, 15, x_38);
lean_ctor_set(x_41, 16, x_35);
lean_ctor_set(x_41, 17, x_39);
lean_ctor_set(x_41, 18, x_29);
lean_ctor_set(x_41, 19, x_30);
lean_ctor_set(x_41, 20, x_40);
lean_ctor_set(x_41, 21, x_40);
lean_inc(x_10);
x_42 = l_Lake_Package_loadFromEnv(x_41, x_10, x_16, x_11, x_23);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 0);
if (lean_is_scalar(x_24)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_24;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
lean_ctor_set(x_43, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
if (lean_is_scalar(x_24)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_24;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_10);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_42, 0, x_52);
return x_42;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_24;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_10);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_24);
lean_dec(x_10);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_42, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_42, 0, x_65);
return x_42;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
lean_dec(x_42);
x_67 = lean_ctor_get(x_43, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_43, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_69 = x_43;
} else {
 lean_dec_ref(x_43);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
}
block_89:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_mk_empty_array_with_capacity(x_76);
x_79 = lean_box(1);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = 0;
lean_inc(x_25);
x_81 = l_Lean_Name_toString(x_25, x_80);
x_82 = l_Lake_loadLeanConfig___closed__0;
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Lake_loadLeanConfig___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = l_Lake_loadLeanConfig___closed__2;
x_87 = lean_string_append(x_85, x_86);
lean_inc_ref_n(x_78, 2);
x_31 = x_73;
x_32 = x_74;
x_33 = x_75;
x_34 = x_79;
x_35 = x_78;
x_36 = x_78;
x_37 = x_77;
x_38 = x_78;
x_39 = x_87;
goto block_72;
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_28, 0);
lean_inc(x_88);
lean_inc_ref_n(x_78, 2);
x_31 = x_73;
x_32 = x_74;
x_33 = x_75;
x_34 = x_79;
x_35 = x_78;
x_36 = x_78;
x_37 = x_77;
x_38 = x_78;
x_39 = x_88;
goto block_72;
}
}
block_100:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = l_System_FilePath_normalize(x_90);
x_92 = lean_unsigned_to_nat(0u);
x_93 = l_Lake_loadLeanConfig___closed__3;
x_94 = lean_box(1);
x_95 = l_Lake_loadLeanConfig___closed__5;
if (x_95 == 0)
{
x_73 = x_93;
x_74 = x_93;
x_75 = x_91;
x_76 = x_92;
x_77 = x_94;
goto block_89;
}
else
{
uint8_t x_96; 
x_96 = l_Lake_loadLeanConfig___closed__6;
if (x_96 == 0)
{
x_73 = x_93;
x_74 = x_93;
x_75 = x_91;
x_76 = x_92;
x_77 = x_94;
goto block_89;
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; 
x_97 = 0;
x_98 = l_Lake_loadLeanConfig___closed__7;
x_99 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(x_25, x_93, x_97, x_98, x_94);
x_73 = x_93;
x_74 = x_93;
x_75 = x_91;
x_76 = x_92;
x_77 = x_99;
goto block_89;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
x_103 = lean_ctor_get(x_20, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_dec_ref(x_20);
x_105 = lean_io_error_to_string(x_103);
x_106 = 3;
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_106);
x_108 = lean_array_get_size(x_11);
x_109 = lean_array_push(x_11, x_107);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_109);
lean_ctor_set(x_5, 0, x_108);
lean_ctor_set(x_4, 1, x_104);
return x_4;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_5, 0);
x_111 = lean_ctor_get(x_5, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_5);
x_112 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_1, 10);
lean_inc(x_116);
x_117 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_118);
lean_dec_ref(x_1);
lean_inc(x_110);
x_119 = l_Lake_PackageDecl_loadFromEnv(x_110, x_116);
x_120 = l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(x_119, x_7);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_177; 
lean_free_object(x_4);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 2);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_ctor_get(x_122, 2);
x_128 = lean_ctor_get(x_122, 12);
x_129 = lean_ctor_get(x_122, 13);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_122, 15);
lean_inc_ref(x_130);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_188; 
x_188 = l_Lake_loadLeanConfig___closed__8;
x_177 = x_188;
goto block_187;
}
else
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_127, 0);
lean_inc(x_189);
x_177 = x_189;
goto block_187;
}
block_159:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_126);
lean_ctor_set(x_141, 2, x_113);
lean_ctor_set(x_141, 3, x_112);
lean_ctor_set(x_141, 4, x_122);
lean_ctor_set(x_141, 5, x_115);
lean_ctor_set(x_141, 6, x_114);
lean_ctor_set(x_141, 7, x_133);
lean_ctor_set(x_141, 8, x_117);
lean_ctor_set(x_141, 9, x_118);
lean_ctor_set(x_141, 10, x_131);
lean_ctor_set(x_141, 11, x_132);
lean_ctor_set(x_141, 12, x_137);
lean_ctor_set(x_141, 13, x_136);
lean_ctor_set(x_141, 14, x_134);
lean_ctor_set(x_141, 15, x_138);
lean_ctor_set(x_141, 16, x_135);
lean_ctor_set(x_141, 17, x_139);
lean_ctor_set(x_141, 18, x_129);
lean_ctor_set(x_141, 19, x_130);
lean_ctor_set(x_141, 20, x_140);
lean_ctor_set(x_141, 21, x_140);
lean_inc(x_110);
x_142 = l_Lake_Package_loadFromEnv(x_141, x_110, x_116, x_111, x_123);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_124;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_110);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
if (lean_is_scalar(x_145)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_145;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_144);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_124);
lean_dec(x_110);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_153 = x_142;
} else {
 lean_dec_ref(x_142);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_143, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_143, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_156 = x_143;
} else {
 lean_dec_ref(x_143);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_152);
return x_158;
}
}
block_176:
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_mk_empty_array_with_capacity(x_163);
x_166 = lean_box(1);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = 0;
lean_inc(x_125);
x_168 = l_Lean_Name_toString(x_125, x_167);
x_169 = l_Lake_loadLeanConfig___closed__0;
x_170 = lean_string_append(x_168, x_169);
x_171 = l_Lake_loadLeanConfig___closed__1;
x_172 = lean_string_append(x_170, x_171);
x_173 = l_Lake_loadLeanConfig___closed__2;
x_174 = lean_string_append(x_172, x_173);
lean_inc_ref_n(x_165, 2);
x_131 = x_160;
x_132 = x_161;
x_133 = x_162;
x_134 = x_166;
x_135 = x_165;
x_136 = x_165;
x_137 = x_164;
x_138 = x_165;
x_139 = x_174;
goto block_159;
}
else
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_128, 0);
lean_inc(x_175);
lean_inc_ref_n(x_165, 2);
x_131 = x_160;
x_132 = x_161;
x_133 = x_162;
x_134 = x_166;
x_135 = x_165;
x_136 = x_165;
x_137 = x_164;
x_138 = x_165;
x_139 = x_175;
goto block_159;
}
}
block_187:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = l_System_FilePath_normalize(x_177);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Lake_loadLeanConfig___closed__3;
x_181 = lean_box(1);
x_182 = l_Lake_loadLeanConfig___closed__5;
if (x_182 == 0)
{
x_160 = x_180;
x_161 = x_180;
x_162 = x_178;
x_163 = x_179;
x_164 = x_181;
goto block_176;
}
else
{
uint8_t x_183; 
x_183 = l_Lake_loadLeanConfig___closed__6;
if (x_183 == 0)
{
x_160 = x_180;
x_161 = x_180;
x_162 = x_178;
x_163 = x_179;
x_164 = x_181;
goto block_176;
}
else
{
size_t x_184; size_t x_185; lean_object* x_186; 
x_184 = 0;
x_185 = l_Lake_loadLeanConfig___closed__7;
x_186 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(x_125, x_180, x_184, x_185, x_181);
x_160 = x_180;
x_161 = x_180;
x_162 = x_178;
x_163 = x_179;
x_164 = x_186;
goto block_176;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec(x_110);
x_190 = lean_ctor_get(x_120, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_120, 1);
lean_inc(x_191);
lean_dec_ref(x_120);
x_192 = lean_io_error_to_string(x_190);
x_193 = 3;
x_194 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_193);
x_195 = lean_array_get_size(x_111);
x_196 = lean_array_push(x_111, x_194);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_4, 1, x_191);
lean_ctor_set(x_4, 0, x_197);
return x_4;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_198 = lean_ctor_get(x_4, 1);
lean_inc(x_198);
lean_dec(x_4);
x_199 = lean_ctor_get(x_5, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_5, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_201 = x_5;
} else {
 lean_dec_ref(x_5);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_1, 10);
lean_inc(x_206);
x_207 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_208);
lean_dec_ref(x_1);
lean_inc(x_199);
x_209 = l_Lake_PackageDecl_loadFromEnv(x_199, x_206);
x_210 = l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(x_209, x_198);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_267; 
lean_dec(x_201);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 2);
lean_inc_ref(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_211, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_211, 1);
lean_inc(x_216);
lean_dec(x_211);
x_217 = lean_ctor_get(x_212, 2);
x_218 = lean_ctor_get(x_212, 12);
x_219 = lean_ctor_get(x_212, 13);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_212, 15);
lean_inc_ref(x_220);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_278; 
x_278 = l_Lake_loadLeanConfig___closed__8;
x_267 = x_278;
goto block_277;
}
else
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_217, 0);
lean_inc(x_279);
x_267 = x_279;
goto block_277;
}
block_249:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_box(0);
x_231 = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(x_231, 0, x_215);
lean_ctor_set(x_231, 1, x_216);
lean_ctor_set(x_231, 2, x_203);
lean_ctor_set(x_231, 3, x_202);
lean_ctor_set(x_231, 4, x_212);
lean_ctor_set(x_231, 5, x_205);
lean_ctor_set(x_231, 6, x_204);
lean_ctor_set(x_231, 7, x_223);
lean_ctor_set(x_231, 8, x_207);
lean_ctor_set(x_231, 9, x_208);
lean_ctor_set(x_231, 10, x_221);
lean_ctor_set(x_231, 11, x_222);
lean_ctor_set(x_231, 12, x_227);
lean_ctor_set(x_231, 13, x_226);
lean_ctor_set(x_231, 14, x_224);
lean_ctor_set(x_231, 15, x_228);
lean_ctor_set(x_231, 16, x_225);
lean_ctor_set(x_231, 17, x_229);
lean_ctor_set(x_231, 18, x_219);
lean_ctor_set(x_231, 19, x_220);
lean_ctor_set(x_231, 20, x_230);
lean_ctor_set(x_231, 21, x_230);
lean_inc(x_199);
x_232 = l_Lake_Package_loadFromEnv(x_231, x_199, x_206, x_200, x_213);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_214;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_199);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
if (lean_is_scalar(x_235)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_235;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_234);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_214);
lean_dec(x_199);
x_242 = lean_ctor_get(x_232, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_243 = x_232;
} else {
 lean_dec_ref(x_232);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_233, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_233, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_246 = x_233;
} else {
 lean_dec_ref(x_233);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
if (lean_is_scalar(x_243)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_243;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_242);
return x_248;
}
}
block_266:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_mk_empty_array_with_capacity(x_253);
x_256 = lean_box(1);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_257 = 0;
lean_inc(x_215);
x_258 = l_Lean_Name_toString(x_215, x_257);
x_259 = l_Lake_loadLeanConfig___closed__0;
x_260 = lean_string_append(x_258, x_259);
x_261 = l_Lake_loadLeanConfig___closed__1;
x_262 = lean_string_append(x_260, x_261);
x_263 = l_Lake_loadLeanConfig___closed__2;
x_264 = lean_string_append(x_262, x_263);
lean_inc_ref_n(x_255, 2);
x_221 = x_250;
x_222 = x_251;
x_223 = x_252;
x_224 = x_256;
x_225 = x_255;
x_226 = x_255;
x_227 = x_254;
x_228 = x_255;
x_229 = x_264;
goto block_249;
}
else
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_218, 0);
lean_inc(x_265);
lean_inc_ref_n(x_255, 2);
x_221 = x_250;
x_222 = x_251;
x_223 = x_252;
x_224 = x_256;
x_225 = x_255;
x_226 = x_255;
x_227 = x_254;
x_228 = x_255;
x_229 = x_265;
goto block_249;
}
}
block_277:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_268 = l_System_FilePath_normalize(x_267);
x_269 = lean_unsigned_to_nat(0u);
x_270 = l_Lake_loadLeanConfig___closed__3;
x_271 = lean_box(1);
x_272 = l_Lake_loadLeanConfig___closed__5;
if (x_272 == 0)
{
x_250 = x_270;
x_251 = x_270;
x_252 = x_268;
x_253 = x_269;
x_254 = x_271;
goto block_266;
}
else
{
uint8_t x_273; 
x_273 = l_Lake_loadLeanConfig___closed__6;
if (x_273 == 0)
{
x_250 = x_270;
x_251 = x_270;
x_252 = x_268;
x_253 = x_269;
x_254 = x_271;
goto block_266;
}
else
{
size_t x_274; size_t x_275; lean_object* x_276; 
x_274 = 0;
x_275 = l_Lake_loadLeanConfig___closed__7;
x_276 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(x_215, x_270, x_274, x_275, x_271);
x_250 = x_270;
x_251 = x_270;
x_252 = x_268;
x_253 = x_269;
x_254 = x_276;
goto block_266;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec_ref(x_202);
lean_dec(x_199);
x_280 = lean_ctor_get(x_210, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_210, 1);
lean_inc(x_281);
lean_dec_ref(x_210);
x_282 = lean_io_error_to_string(x_280);
x_283 = 3;
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_283);
x_285 = lean_array_get_size(x_200);
x_286 = lean_array_push(x_200, x_284);
if (lean_is_scalar(x_201)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_201;
 lean_ctor_set_tag(x_287, 1);
}
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_281);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec_ref(x_1);
x_289 = !lean_is_exclusive(x_4);
if (x_289 == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = lean_ctor_get(x_4, 0);
lean_dec(x_290);
x_291 = !lean_is_exclusive(x_5);
if (x_291 == 0)
{
return x_4;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_5, 0);
x_293 = lean_ctor_get(x_5, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_5);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_4, 0, x_294);
return x_4;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_295 = lean_ctor_get(x_4, 1);
lean_inc(x_295);
lean_dec(x_4);
x_296 = lean_ctor_get(x_5, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_5, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_298 = x_5;
} else {
 lean_dec_ref(x_5);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_295);
return x_300;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_loadLeanConfig___closed__0 = _init_l_Lake_loadLeanConfig___closed__0();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__0);
l_Lake_loadLeanConfig___closed__1 = _init_l_Lake_loadLeanConfig___closed__1();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__1);
l_Lake_loadLeanConfig___closed__2 = _init_l_Lake_loadLeanConfig___closed__2();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__2);
l_Lake_loadLeanConfig___closed__3 = _init_l_Lake_loadLeanConfig___closed__3();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__3);
l_Lake_loadLeanConfig___closed__4 = _init_l_Lake_loadLeanConfig___closed__4();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__4);
l_Lake_loadLeanConfig___closed__5 = _init_l_Lake_loadLeanConfig___closed__5();
l_Lake_loadLeanConfig___closed__6 = _init_l_Lake_loadLeanConfig___closed__6();
l_Lake_loadLeanConfig___closed__7 = _init_l_Lake_loadLeanConfig___closed__7();
l_Lake_loadLeanConfig___closed__8 = _init_l_Lake_loadLeanConfig___closed__8();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
