// Lean compiler output
// Module: Lake.Load.Lean
// Imports: Lean.Environment Lake.Config.Package Lake.Load.Config Lake.Load.Lean.Elab Lake.Load.Lean.Eval
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 9);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
lean_inc(x_8);
x_17 = l_Lake_PackageDecl_loadFromEnv(x_8, x_14);
x_18 = l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(x_17, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_87; 
lean_free_object(x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_ctor_get(x_20, 12);
x_26 = lean_ctor_get(x_20, 13);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_20, 15);
lean_inc_ref(x_27);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_98; 
x_98 = l_Lake_loadLeanConfig___closed__8;
x_87 = x_98;
goto block_97;
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_24, 0);
lean_inc(x_99);
x_87 = x_99;
goto block_97;
}
block_69:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 20, 0);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_11);
lean_ctor_set(x_38, 2, x_10);
lean_ctor_set(x_38, 3, x_20);
lean_ctor_set(x_38, 4, x_13);
lean_ctor_set(x_38, 5, x_12);
lean_ctor_set(x_38, 6, x_33);
lean_ctor_set(x_38, 7, x_15);
lean_ctor_set(x_38, 8, x_16);
lean_ctor_set(x_38, 9, x_30);
lean_ctor_set(x_38, 10, x_28);
lean_ctor_set(x_38, 11, x_32);
lean_ctor_set(x_38, 12, x_29);
lean_ctor_set(x_38, 13, x_34);
lean_ctor_set(x_38, 14, x_31);
lean_ctor_set(x_38, 15, x_35);
lean_ctor_set(x_38, 16, x_36);
lean_ctor_set(x_38, 17, x_26);
lean_ctor_set(x_38, 18, x_27);
lean_ctor_set(x_38, 19, x_37);
lean_inc(x_8);
x_39 = l_Lake_Package_loadFromEnv(x_38, x_8, x_14, x_9, x_21);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_40, 0);
if (lean_is_scalar(x_23)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_23;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_8);
lean_ctor_set(x_40, 0, x_45);
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
if (lean_is_scalar(x_23)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_23;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_8);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_39, 0, x_49);
return x_39;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_53 = x_40;
} else {
 lean_dec_ref(x_40);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_23;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_8);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_39, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_39;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = lean_ctor_get(x_40, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_66 = x_40;
} else {
 lean_dec_ref(x_40);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
}
block_86:
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_mk_empty_array_with_capacity(x_71);
x_76 = lean_box(1);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = 0;
lean_inc(x_22);
x_78 = l_Lean_Name_toString(x_22, x_77);
x_79 = l_Lake_loadLeanConfig___closed__0;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lake_loadLeanConfig___closed__1;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Lake_loadLeanConfig___closed__2;
x_84 = lean_string_append(x_82, x_83);
lean_inc_ref_n(x_75, 2);
x_28 = x_70;
x_29 = x_75;
x_30 = x_72;
x_31 = x_75;
x_32 = x_74;
x_33 = x_73;
x_34 = x_76;
x_35 = x_75;
x_36 = x_84;
goto block_69;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_25, 0);
lean_inc(x_85);
lean_inc_ref_n(x_75, 2);
x_28 = x_70;
x_29 = x_75;
x_30 = x_72;
x_31 = x_75;
x_32 = x_74;
x_33 = x_73;
x_34 = x_76;
x_35 = x_75;
x_36 = x_85;
goto block_69;
}
}
block_97:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = l_System_FilePath_normalize(x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lake_loadLeanConfig___closed__3;
x_91 = lean_box(1);
x_92 = l_Lake_loadLeanConfig___closed__5;
if (x_92 == 0)
{
x_70 = x_90;
x_71 = x_89;
x_72 = x_90;
x_73 = x_88;
x_74 = x_91;
goto block_86;
}
else
{
uint8_t x_93; 
x_93 = l_Lake_loadLeanConfig___closed__6;
if (x_93 == 0)
{
x_70 = x_90;
x_71 = x_89;
x_72 = x_90;
x_73 = x_88;
x_74 = x_91;
goto block_86;
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; 
x_94 = 0;
x_95 = l_Lake_loadLeanConfig___closed__7;
x_96 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(x_22, x_90, x_94, x_95, x_91);
x_70 = x_90;
x_71 = x_89;
x_72 = x_90;
x_73 = x_88;
x_74 = x_96;
goto block_86;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
x_100 = !lean_is_exclusive(x_18);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_18, 0);
x_102 = lean_io_error_to_string(x_101);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_get_size(x_9);
x_106 = lean_array_push(x_9, x_104);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_106);
lean_ctor_set(x_5, 0, x_105);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get(x_18, 0);
x_108 = lean_ctor_get(x_18, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_18);
x_109 = lean_io_error_to_string(x_107);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_9);
x_113 = lean_array_push(x_9, x_111);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_113);
lean_ctor_set(x_5, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_5);
lean_ctor_set(x_114, 1, x_108);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_115 = lean_ctor_get(x_5, 0);
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_5);
x_117 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_1, 9);
lean_inc(x_121);
x_122 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_123);
lean_dec_ref(x_1);
lean_inc(x_115);
x_124 = l_Lake_PackageDecl_loadFromEnv(x_115, x_121);
x_125 = l_IO_ofExcept___at___Lake_loadLeanConfig_spec__0___redArg(x_124, x_6);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_181; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 1);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec_ref(x_125);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 2);
x_132 = lean_ctor_get(x_127, 12);
x_133 = lean_ctor_get(x_127, 13);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_127, 15);
lean_inc_ref(x_134);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_192; 
x_192 = l_Lake_loadLeanConfig___closed__8;
x_181 = x_192;
goto block_191;
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_131, 0);
lean_inc(x_193);
x_181 = x_193;
goto block_191;
}
block_163:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 20, 0);
lean_ctor_set(x_145, 0, x_129);
lean_ctor_set(x_145, 1, x_118);
lean_ctor_set(x_145, 2, x_117);
lean_ctor_set(x_145, 3, x_127);
lean_ctor_set(x_145, 4, x_120);
lean_ctor_set(x_145, 5, x_119);
lean_ctor_set(x_145, 6, x_140);
lean_ctor_set(x_145, 7, x_122);
lean_ctor_set(x_145, 8, x_123);
lean_ctor_set(x_145, 9, x_137);
lean_ctor_set(x_145, 10, x_135);
lean_ctor_set(x_145, 11, x_139);
lean_ctor_set(x_145, 12, x_136);
lean_ctor_set(x_145, 13, x_141);
lean_ctor_set(x_145, 14, x_138);
lean_ctor_set(x_145, 15, x_142);
lean_ctor_set(x_145, 16, x_143);
lean_ctor_set(x_145, 17, x_133);
lean_ctor_set(x_145, 18, x_134);
lean_ctor_set(x_145, 19, x_144);
lean_inc(x_115);
x_146 = l_Lake_Package_loadFromEnv(x_145, x_115, x_121, x_116, x_128);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_152 = x_147;
} else {
 lean_dec_ref(x_147);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_130;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_115);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
if (lean_is_scalar(x_149)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_149;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_148);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_130);
lean_dec(x_115);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_147, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_147, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_160 = x_147;
} else {
 lean_dec_ref(x_147);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
if (lean_is_scalar(x_157)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_157;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_156);
return x_162;
}
}
block_180:
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_mk_empty_array_with_capacity(x_165);
x_170 = lean_box(1);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = 0;
lean_inc(x_129);
x_172 = l_Lean_Name_toString(x_129, x_171);
x_173 = l_Lake_loadLeanConfig___closed__0;
x_174 = lean_string_append(x_172, x_173);
x_175 = l_Lake_loadLeanConfig___closed__1;
x_176 = lean_string_append(x_174, x_175);
x_177 = l_Lake_loadLeanConfig___closed__2;
x_178 = lean_string_append(x_176, x_177);
lean_inc_ref_n(x_169, 2);
x_135 = x_164;
x_136 = x_169;
x_137 = x_166;
x_138 = x_169;
x_139 = x_168;
x_140 = x_167;
x_141 = x_170;
x_142 = x_169;
x_143 = x_178;
goto block_163;
}
else
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_132, 0);
lean_inc(x_179);
lean_inc_ref_n(x_169, 2);
x_135 = x_164;
x_136 = x_169;
x_137 = x_166;
x_138 = x_169;
x_139 = x_168;
x_140 = x_167;
x_141 = x_170;
x_142 = x_169;
x_143 = x_179;
goto block_163;
}
}
block_191:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_182 = l_System_FilePath_normalize(x_181);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Lake_loadLeanConfig___closed__3;
x_185 = lean_box(1);
x_186 = l_Lake_loadLeanConfig___closed__5;
if (x_186 == 0)
{
x_164 = x_184;
x_165 = x_183;
x_166 = x_184;
x_167 = x_182;
x_168 = x_185;
goto block_180;
}
else
{
uint8_t x_187; 
x_187 = l_Lake_loadLeanConfig___closed__6;
if (x_187 == 0)
{
x_164 = x_184;
x_165 = x_183;
x_166 = x_184;
x_167 = x_182;
x_168 = x_185;
goto block_180;
}
else
{
size_t x_188; size_t x_189; lean_object* x_190; 
x_188 = 0;
x_189 = l_Lake_loadLeanConfig___closed__7;
x_190 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__2(x_129, x_184, x_188, x_189, x_185);
x_164 = x_184;
x_165 = x_183;
x_166 = x_184;
x_167 = x_182;
x_168 = x_190;
goto block_180;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_115);
x_194 = lean_ctor_get(x_125, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_125, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_196 = x_125;
} else {
 lean_dec_ref(x_125);
 x_196 = lean_box(0);
}
x_197 = lean_io_error_to_string(x_194);
x_198 = 3;
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
x_200 = lean_array_get_size(x_116);
x_201 = lean_array_push(x_116, x_199);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_196;
 lean_ctor_set_tag(x_203, 0);
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_195);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec_ref(x_1);
x_204 = !lean_is_exclusive(x_4);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_4, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_5);
if (x_206 == 0)
{
return x_4;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_5, 0);
x_208 = lean_ctor_get(x_5, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_5);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_4, 0, x_209);
return x_4;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_4, 1);
lean_inc(x_210);
lean_dec(x_4);
x_211 = lean_ctor_get(x_5, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_5, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_213 = x_5;
} else {
 lean_dec_ref(x_5);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
return x_215;
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
