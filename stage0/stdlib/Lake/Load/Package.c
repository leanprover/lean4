// Lean compiler output
// Module: Lake.Load.Package
// Imports: Lake.Load.Lean Lake.Load.Toml
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
static lean_object* l_Lake_loadPackageCore___closed__2;
static lean_object* l_Lake_loadPackageCore___closed__4;
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__0;
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__3;
static lean_object* l_Lake_loadPackageCore___closed__6;
static lean_object* l_Lake_loadPackageCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object*);
static lean_object* l_Lake_loadPackage___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__1;
static lean_object* l_Lake_configFileExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
static lean_object* _init_l_Lake_configFileExists___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_configFileExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toml", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lake_configFileExists___closed__0;
lean_inc(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_System_FilePath_pathExists(x_5, x_2);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lake_configFileExists___closed__1;
x_11 = l_System_FilePath_addExtension(x_1, x_10);
x_12 = l_System_FilePath_pathExists(x_11, x_9);
lean_dec(x_11);
return x_12;
}
else
{
lean_dec(x_1);
return x_6;
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lake_configFileExists___closed__0;
lean_inc(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_Lake_resolvePath(x_5, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_12 = l_Lake_configFileExists___closed__1;
x_13 = l_System_FilePath_addExtension(x_1, x_12);
x_14 = l_Lake_resolvePath(x_13, x_8);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = l_Lake_resolvePath(x_1, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" are both present; using ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": configuration has unsupported file extension: ", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": configuration file not found: ", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 8);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 9);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_18 = lean_ctor_get(x_2, 10);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 11);
lean_inc(x_19);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 x_20 = x_2;
} else {
 lean_dec_ref(x_2);
 x_20 = lean_box(0);
}
lean_inc(x_10);
x_21 = l_System_FilePath_extension(x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_11);
x_22 = l_Lake_configFileExists___closed__0;
lean_inc(x_10);
x_23 = l_System_FilePath_addExtension(x_10, x_22);
lean_inc(x_9);
x_24 = l_Lake_joinRelative(x_9, x_23);
lean_inc(x_24);
x_25 = l_Lake_resolvePath(x_24, x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lake_configFileExists___closed__1;
x_30 = l_System_FilePath_addExtension(x_10, x_29);
lean_inc(x_9);
x_31 = l_Lake_joinRelative(x_9, x_30);
x_32 = lean_string_utf8_byte_size(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_84; 
lean_free_object(x_25);
lean_dec(x_24);
x_35 = l_System_FilePath_pathExists(x_31, x_28);
lean_dec(x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_84 = lean_unbox(x_36);
lean_dec(x_36);
if (x_84 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
x_38 = x_3;
goto block_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_85 = l_Lake_loadPackageCore___closed__0;
x_86 = lean_string_append(x_1, x_85);
x_87 = lean_string_append(x_86, x_23);
x_88 = l_Lake_loadPackageCore___closed__1;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_30);
lean_dec(x_30);
x_91 = l_Lake_loadPackageCore___closed__2;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_23);
x_94 = lean_box(1);
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
x_96 = lean_unbox(x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_96);
x_97 = lean_array_push(x_3, x_95);
x_38 = x_97;
goto block_83;
}
block_83:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_20)) {
 x_39 = lean_alloc_ctor(0, 12, 3);
} else {
 x_39 = x_20;
}
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_6);
lean_ctor_set(x_39, 2, x_7);
lean_ctor_set(x_39, 3, x_8);
lean_ctor_set(x_39, 4, x_9);
lean_ctor_set(x_39, 5, x_23);
lean_ctor_set(x_39, 6, x_27);
lean_ctor_set(x_39, 7, x_12);
lean_ctor_set(x_39, 8, x_13);
lean_ctor_set(x_39, 9, x_14);
lean_ctor_set(x_39, 10, x_18);
lean_ctor_set(x_39, 11, x_19);
lean_ctor_set_uint8(x_39, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_39, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_39, sizeof(void*)*12 + 2, x_17);
x_40 = l_Lake_loadLeanConfig(x_39, x_38, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 1);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_42, 1, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_41, 0, x_53);
return x_40;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_dec(x_41);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_40, 0, x_60);
return x_40;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_dec(x_40);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_63 = x_41;
} else {
 lean_dec_ref(x_41);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_42, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_42, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_66 = x_42;
} else {
 lean_dec_ref(x_42);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_61);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_40);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_40, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_41);
if (x_73 == 0)
{
return x_40;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_41, 0);
x_75 = lean_ctor_get(x_41, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_40, 0, x_76);
return x_40;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_40, 1);
lean_inc(x_77);
lean_dec(x_40);
x_78 = lean_ctor_get(x_41, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_41, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_80 = x_41;
} else {
 lean_dec_ref(x_41);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
}
else
{
lean_object* x_98; uint8_t x_99; 
lean_dec(x_27);
lean_dec(x_23);
lean_inc(x_31);
x_98 = l_Lake_resolvePath(x_31, x_28);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = lean_string_utf8_byte_size(x_100);
x_103 = lean_nat_dec_eq(x_102, x_33);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_98);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_1);
if (lean_is_scalar(x_20)) {
 x_104 = lean_alloc_ctor(0, 12, 3);
} else {
 x_104 = x_20;
}
lean_ctor_set(x_104, 0, x_5);
lean_ctor_set(x_104, 1, x_6);
lean_ctor_set(x_104, 2, x_7);
lean_ctor_set(x_104, 3, x_8);
lean_ctor_set(x_104, 4, x_9);
lean_ctor_set(x_104, 5, x_30);
lean_ctor_set(x_104, 6, x_100);
lean_ctor_set(x_104, 7, x_12);
lean_ctor_set(x_104, 8, x_13);
lean_ctor_set(x_104, 9, x_14);
lean_ctor_set(x_104, 10, x_18);
lean_ctor_set(x_104, 11, x_19);
lean_ctor_set_uint8(x_104, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_104, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_104, sizeof(void*)*12 + 2, x_17);
x_105 = l_Lake_loadTomlConfig(x_104, x_3, x_101);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_box(0);
lean_ctor_set(x_25, 1, x_111);
lean_ctor_set(x_25, 0, x_110);
lean_ctor_set(x_106, 0, x_25);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_106, 0);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_106);
x_114 = lean_box(0);
lean_ctor_set(x_25, 1, x_114);
lean_ctor_set(x_25, 0, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_25);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_105, 0, x_115);
return x_105;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_105, 1);
lean_inc(x_116);
lean_dec(x_105);
x_117 = lean_ctor_get(x_106, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_106, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_119 = x_106;
} else {
 lean_dec_ref(x_106);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
lean_ctor_set(x_25, 1, x_120);
lean_ctor_set(x_25, 0, x_117);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_25);
lean_ctor_set(x_121, 1, x_118);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_free_object(x_25);
x_123 = !lean_is_exclusive(x_105);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_105, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_106);
if (x_125 == 0)
{
return x_105;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_106, 0);
x_127 = lean_ctor_get(x_106, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_106);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_105, 0, x_128);
return x_105;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_105, 1);
lean_inc(x_129);
lean_dec(x_105);
x_130 = lean_ctor_get(x_106, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_106, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_132 = x_106;
} else {
 lean_dec_ref(x_106);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_100);
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_135 = l_Lake_loadPackageCore___closed__3;
x_136 = lean_string_append(x_1, x_135);
x_137 = lean_string_append(x_136, x_24);
lean_dec(x_24);
x_138 = l_Lake_loadPackageCore___closed__4;
x_139 = lean_string_append(x_137, x_138);
x_140 = lean_string_append(x_139, x_31);
lean_dec(x_31);
x_141 = lean_box(3);
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_unbox(x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_143);
x_144 = lean_array_get_size(x_3);
x_145 = lean_array_push(x_3, x_142);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_145);
lean_ctor_set(x_25, 0, x_144);
lean_ctor_set(x_98, 0, x_25);
return x_98;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_98, 0);
x_147 = lean_ctor_get(x_98, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_98);
x_148 = lean_string_utf8_byte_size(x_146);
x_149 = lean_nat_dec_eq(x_148, x_33);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_1);
if (lean_is_scalar(x_20)) {
 x_150 = lean_alloc_ctor(0, 12, 3);
} else {
 x_150 = x_20;
}
lean_ctor_set(x_150, 0, x_5);
lean_ctor_set(x_150, 1, x_6);
lean_ctor_set(x_150, 2, x_7);
lean_ctor_set(x_150, 3, x_8);
lean_ctor_set(x_150, 4, x_9);
lean_ctor_set(x_150, 5, x_30);
lean_ctor_set(x_150, 6, x_146);
lean_ctor_set(x_150, 7, x_12);
lean_ctor_set(x_150, 8, x_13);
lean_ctor_set(x_150, 9, x_14);
lean_ctor_set(x_150, 10, x_18);
lean_ctor_set(x_150, 11, x_19);
lean_ctor_set_uint8(x_150, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_150, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_150, sizeof(void*)*12 + 2, x_17);
x_151 = l_Lake_loadTomlConfig(x_150, x_3, x_147);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_157 = x_152;
} else {
 lean_dec_ref(x_152);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
lean_ctor_set(x_25, 1, x_158);
lean_ctor_set(x_25, 0, x_155);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_25);
lean_ctor_set(x_159, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_153);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_free_object(x_25);
x_161 = lean_ctor_get(x_151, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_162 = x_151;
} else {
 lean_dec_ref(x_151);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_165 = x_152;
} else {
 lean_dec_ref(x_152);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_146);
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_168 = l_Lake_loadPackageCore___closed__3;
x_169 = lean_string_append(x_1, x_168);
x_170 = lean_string_append(x_169, x_24);
lean_dec(x_24);
x_171 = l_Lake_loadPackageCore___closed__4;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_string_append(x_172, x_31);
lean_dec(x_31);
x_174 = lean_box(3);
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
x_176 = lean_unbox(x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_176);
x_177 = lean_array_get_size(x_3);
x_178 = lean_array_push(x_3, x_175);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_178);
lean_ctor_set(x_25, 0, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_25);
lean_ctor_set(x_179, 1, x_147);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_180 = lean_ctor_get(x_25, 0);
x_181 = lean_ctor_get(x_25, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_25);
x_182 = l_Lake_configFileExists___closed__1;
x_183 = l_System_FilePath_addExtension(x_10, x_182);
lean_inc(x_9);
x_184 = l_Lake_joinRelative(x_9, x_183);
x_185 = lean_string_utf8_byte_size(x_180);
x_186 = lean_unsigned_to_nat(0u);
x_187 = lean_nat_dec_eq(x_185, x_186);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_215; 
lean_dec(x_24);
x_188 = l_System_FilePath_pathExists(x_184, x_181);
lean_dec(x_184);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_215 = lean_unbox(x_189);
lean_dec(x_189);
if (x_215 == 0)
{
lean_dec(x_183);
lean_dec(x_1);
x_191 = x_3;
goto block_214;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; 
x_216 = l_Lake_loadPackageCore___closed__0;
x_217 = lean_string_append(x_1, x_216);
x_218 = lean_string_append(x_217, x_23);
x_219 = l_Lake_loadPackageCore___closed__1;
x_220 = lean_string_append(x_218, x_219);
x_221 = lean_string_append(x_220, x_183);
lean_dec(x_183);
x_222 = l_Lake_loadPackageCore___closed__2;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_string_append(x_223, x_23);
x_225 = lean_box(1);
x_226 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_226, 0, x_224);
x_227 = lean_unbox(x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*1, x_227);
x_228 = lean_array_push(x_3, x_226);
x_191 = x_228;
goto block_214;
}
block_214:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
if (lean_is_scalar(x_20)) {
 x_192 = lean_alloc_ctor(0, 12, 3);
} else {
 x_192 = x_20;
}
lean_ctor_set(x_192, 0, x_5);
lean_ctor_set(x_192, 1, x_6);
lean_ctor_set(x_192, 2, x_7);
lean_ctor_set(x_192, 3, x_8);
lean_ctor_set(x_192, 4, x_9);
lean_ctor_set(x_192, 5, x_23);
lean_ctor_set(x_192, 6, x_180);
lean_ctor_set(x_192, 7, x_12);
lean_ctor_set(x_192, 8, x_13);
lean_ctor_set(x_192, 9, x_14);
lean_ctor_set(x_192, 10, x_18);
lean_ctor_set(x_192, 11, x_19);
lean_ctor_set_uint8(x_192, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_192, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_192, sizeof(void*)*12 + 2, x_17);
x_193 = l_Lake_loadLeanConfig(x_192, x_191, x_190);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_197 = x_193;
} else {
 lean_dec_ref(x_193);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_199 = x_194;
} else {
 lean_dec_ref(x_194);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_201);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_200);
lean_ctor_set(x_204, 1, x_203);
if (lean_is_scalar(x_199)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_199;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_198);
if (lean_is_scalar(x_197)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_197;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_196);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_207 = lean_ctor_get(x_193, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_208 = x_193;
} else {
 lean_dec_ref(x_193);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_194, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_194, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_211 = x_194;
} else {
 lean_dec_ref(x_194);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
if (lean_is_scalar(x_208)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_208;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_207);
return x_213;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec(x_180);
lean_dec(x_23);
lean_inc(x_184);
x_229 = l_Lake_resolvePath(x_184, x_181);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_232 = x_229;
} else {
 lean_dec_ref(x_229);
 x_232 = lean_box(0);
}
x_233 = lean_string_utf8_byte_size(x_230);
x_234 = lean_nat_dec_eq(x_233, x_186);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_232);
lean_dec(x_184);
lean_dec(x_24);
lean_dec(x_1);
if (lean_is_scalar(x_20)) {
 x_235 = lean_alloc_ctor(0, 12, 3);
} else {
 x_235 = x_20;
}
lean_ctor_set(x_235, 0, x_5);
lean_ctor_set(x_235, 1, x_6);
lean_ctor_set(x_235, 2, x_7);
lean_ctor_set(x_235, 3, x_8);
lean_ctor_set(x_235, 4, x_9);
lean_ctor_set(x_235, 5, x_183);
lean_ctor_set(x_235, 6, x_230);
lean_ctor_set(x_235, 7, x_12);
lean_ctor_set(x_235, 8, x_13);
lean_ctor_set(x_235, 9, x_14);
lean_ctor_set(x_235, 10, x_18);
lean_ctor_set(x_235, 11, x_19);
lean_ctor_set_uint8(x_235, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_235, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_235, sizeof(void*)*12 + 2, x_17);
x_236 = l_Lake_loadTomlConfig(x_235, x_3, x_231);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_242 = x_237;
} else {
 lean_dec_ref(x_237);
 x_242 = lean_box(0);
}
x_243 = lean_box(0);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_243);
if (lean_is_scalar(x_242)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_242;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
if (lean_is_scalar(x_239)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_239;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_238);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_ctor_get(x_236, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_248 = x_236;
} else {
 lean_dec_ref(x_236);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_237, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_237, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_251 = x_237;
} else {
 lean_dec_ref(x_237);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
if (lean_is_scalar(x_248)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_248;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_247);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_230);
lean_dec(x_183);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_254 = l_Lake_loadPackageCore___closed__3;
x_255 = lean_string_append(x_1, x_254);
x_256 = lean_string_append(x_255, x_24);
lean_dec(x_24);
x_257 = l_Lake_loadPackageCore___closed__4;
x_258 = lean_string_append(x_256, x_257);
x_259 = lean_string_append(x_258, x_184);
lean_dec(x_184);
x_260 = lean_box(3);
x_261 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_261, 0, x_259);
x_262 = lean_unbox(x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*1, x_262);
x_263 = lean_array_get_size(x_3);
x_264 = lean_array_push(x_3, x_261);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
if (lean_is_scalar(x_232)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_232;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_231);
return x_266;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_267 = lean_ctor_get(x_21, 0);
lean_inc(x_267);
lean_dec(x_21);
lean_inc(x_11);
x_268 = l_Lake_resolvePath(x_11, x_4);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_268, 1);
x_272 = lean_string_utf8_byte_size(x_270);
x_273 = lean_unsigned_to_nat(0u);
x_274 = lean_nat_dec_eq(x_272, x_273);
lean_dec(x_272);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_11);
lean_inc(x_270);
if (lean_is_scalar(x_20)) {
 x_275 = lean_alloc_ctor(0, 12, 3);
} else {
 x_275 = x_20;
}
lean_ctor_set(x_275, 0, x_5);
lean_ctor_set(x_275, 1, x_6);
lean_ctor_set(x_275, 2, x_7);
lean_ctor_set(x_275, 3, x_8);
lean_ctor_set(x_275, 4, x_9);
lean_ctor_set(x_275, 5, x_10);
lean_ctor_set(x_275, 6, x_270);
lean_ctor_set(x_275, 7, x_12);
lean_ctor_set(x_275, 8, x_13);
lean_ctor_set(x_275, 9, x_14);
lean_ctor_set(x_275, 10, x_18);
lean_ctor_set(x_275, 11, x_19);
lean_ctor_set_uint8(x_275, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_275, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_275, sizeof(void*)*12 + 2, x_17);
x_276 = l_Lake_configFileExists___closed__0;
x_277 = lean_string_dec_eq(x_267, x_276);
if (x_277 == 0)
{
lean_object* x_278; uint8_t x_279; 
x_278 = l_Lake_configFileExists___closed__1;
x_279 = lean_string_dec_eq(x_267, x_278);
lean_dec(x_267);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_275);
x_280 = l_Lake_loadPackageCore___closed__5;
x_281 = lean_string_append(x_1, x_280);
x_282 = lean_string_append(x_281, x_270);
lean_dec(x_270);
x_283 = lean_box(3);
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
x_285 = lean_unbox(x_283);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_285);
x_286 = lean_array_get_size(x_3);
x_287 = lean_array_push(x_3, x_284);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_268, 0, x_288);
return x_268;
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_free_object(x_268);
lean_dec(x_270);
lean_dec(x_1);
x_289 = l_Lake_loadTomlConfig(x_275, x_3, x_271);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
if (lean_obj_tag(x_290) == 0)
{
uint8_t x_291; 
x_291 = !lean_is_exclusive(x_289);
if (x_291 == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_289, 0);
lean_dec(x_292);
x_293 = !lean_is_exclusive(x_290);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_290, 0);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
lean_ctor_set(x_290, 0, x_296);
return x_289;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_297 = lean_ctor_get(x_290, 0);
x_298 = lean_ctor_get(x_290, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_290);
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_298);
lean_ctor_set(x_289, 0, x_301);
return x_289;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_289, 1);
lean_inc(x_302);
lean_dec(x_289);
x_303 = lean_ctor_get(x_290, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_290, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_305 = x_290;
} else {
 lean_dec_ref(x_290);
 x_305 = lean_box(0);
}
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_306);
if (lean_is_scalar(x_305)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_305;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_304);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_302);
return x_309;
}
}
else
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_289);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_289, 0);
lean_dec(x_311);
x_312 = !lean_is_exclusive(x_290);
if (x_312 == 0)
{
return x_289;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_290, 0);
x_314 = lean_ctor_get(x_290, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_290);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set(x_289, 0, x_315);
return x_289;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_316 = lean_ctor_get(x_289, 1);
lean_inc(x_316);
lean_dec(x_289);
x_317 = lean_ctor_get(x_290, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_290, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_319 = x_290;
} else {
 lean_dec_ref(x_290);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_316);
return x_321;
}
}
}
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_free_object(x_268);
lean_dec(x_270);
lean_dec(x_267);
lean_dec(x_1);
x_322 = l_Lake_loadLeanConfig(x_275, x_3, x_271);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 0)
{
uint8_t x_324; 
x_324 = !lean_is_exclusive(x_322);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; 
x_325 = lean_ctor_get(x_322, 0);
lean_dec(x_325);
x_326 = !lean_is_exclusive(x_323);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_323, 0);
x_328 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_329 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_330 = l_Prod_map___redArg(x_329, x_328, x_327);
lean_ctor_set(x_323, 0, x_330);
return x_322;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_331 = lean_ctor_get(x_323, 0);
x_332 = lean_ctor_get(x_323, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_323);
x_333 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_334 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_335 = l_Prod_map___redArg(x_334, x_333, x_331);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_332);
lean_ctor_set(x_322, 0, x_336);
return x_322;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_337 = lean_ctor_get(x_322, 1);
lean_inc(x_337);
lean_dec(x_322);
x_338 = lean_ctor_get(x_323, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_323, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_340 = x_323;
} else {
 lean_dec_ref(x_323);
 x_340 = lean_box(0);
}
x_341 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_342 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_343 = l_Prod_map___redArg(x_342, x_341, x_338);
if (lean_is_scalar(x_340)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_340;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_339);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_337);
return x_345;
}
}
else
{
uint8_t x_346; 
x_346 = !lean_is_exclusive(x_322);
if (x_346 == 0)
{
lean_object* x_347; uint8_t x_348; 
x_347 = lean_ctor_get(x_322, 0);
lean_dec(x_347);
x_348 = !lean_is_exclusive(x_323);
if (x_348 == 0)
{
return x_322;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_323, 0);
x_350 = lean_ctor_get(x_323, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_323);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set(x_322, 0, x_351);
return x_322;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_352 = lean_ctor_get(x_322, 1);
lean_inc(x_352);
lean_dec(x_322);
x_353 = lean_ctor_get(x_323, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_323, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_355 = x_323;
} else {
 lean_dec_ref(x_323);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_352);
return x_357;
}
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_270);
lean_dec(x_267);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_358 = l_Lake_loadPackageCore___closed__6;
x_359 = lean_string_append(x_1, x_358);
x_360 = lean_string_append(x_359, x_11);
lean_dec(x_11);
x_361 = lean_box(3);
x_362 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_362, 0, x_360);
x_363 = lean_unbox(x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*1, x_363);
x_364 = lean_array_get_size(x_3);
x_365 = lean_array_push(x_3, x_362);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set(x_268, 0, x_366);
return x_268;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_367 = lean_ctor_get(x_268, 0);
x_368 = lean_ctor_get(x_268, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_268);
x_369 = lean_string_utf8_byte_size(x_367);
x_370 = lean_unsigned_to_nat(0u);
x_371 = lean_nat_dec_eq(x_369, x_370);
lean_dec(x_369);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
lean_dec(x_11);
lean_inc(x_367);
if (lean_is_scalar(x_20)) {
 x_372 = lean_alloc_ctor(0, 12, 3);
} else {
 x_372 = x_20;
}
lean_ctor_set(x_372, 0, x_5);
lean_ctor_set(x_372, 1, x_6);
lean_ctor_set(x_372, 2, x_7);
lean_ctor_set(x_372, 3, x_8);
lean_ctor_set(x_372, 4, x_9);
lean_ctor_set(x_372, 5, x_10);
lean_ctor_set(x_372, 6, x_367);
lean_ctor_set(x_372, 7, x_12);
lean_ctor_set(x_372, 8, x_13);
lean_ctor_set(x_372, 9, x_14);
lean_ctor_set(x_372, 10, x_18);
lean_ctor_set(x_372, 11, x_19);
lean_ctor_set_uint8(x_372, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_372, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_372, sizeof(void*)*12 + 2, x_17);
x_373 = l_Lake_configFileExists___closed__0;
x_374 = lean_string_dec_eq(x_267, x_373);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = l_Lake_configFileExists___closed__1;
x_376 = lean_string_dec_eq(x_267, x_375);
lean_dec(x_267);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_372);
x_377 = l_Lake_loadPackageCore___closed__5;
x_378 = lean_string_append(x_1, x_377);
x_379 = lean_string_append(x_378, x_367);
lean_dec(x_367);
x_380 = lean_box(3);
x_381 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_381, 0, x_379);
x_382 = lean_unbox(x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*1, x_382);
x_383 = lean_array_get_size(x_3);
x_384 = lean_array_push(x_3, x_381);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_368);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_367);
lean_dec(x_1);
x_387 = l_Lake_loadTomlConfig(x_372, x_3, x_368);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_390 = x_387;
} else {
 lean_dec_ref(x_387);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_388, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_388, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_393 = x_388;
} else {
 lean_dec_ref(x_388);
 x_393 = lean_box(0);
}
x_394 = lean_box(0);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_391);
lean_ctor_set(x_395, 1, x_394);
if (lean_is_scalar(x_393)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_393;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_392);
if (lean_is_scalar(x_390)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_390;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_389);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_387, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_399 = x_387;
} else {
 lean_dec_ref(x_387);
 x_399 = lean_box(0);
}
x_400 = lean_ctor_get(x_388, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_388, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_402 = x_388;
} else {
 lean_dec_ref(x_388);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
if (lean_is_scalar(x_399)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_399;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_398);
return x_404;
}
}
}
else
{
lean_object* x_405; lean_object* x_406; 
lean_dec(x_367);
lean_dec(x_267);
lean_dec(x_1);
x_405 = l_Lake_loadLeanConfig(x_372, x_3, x_368);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_408 = x_405;
} else {
 lean_dec_ref(x_405);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_406, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_406, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_411 = x_406;
} else {
 lean_dec_ref(x_406);
 x_411 = lean_box(0);
}
x_412 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_413 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_414 = l_Prod_map___redArg(x_413, x_412, x_409);
if (lean_is_scalar(x_411)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_411;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_410);
if (lean_is_scalar(x_408)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_408;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_407);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_417 = lean_ctor_get(x_405, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_418 = x_405;
} else {
 lean_dec_ref(x_405);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_406, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_406, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_421 = x_406;
} else {
 lean_dec_ref(x_406);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
if (lean_is_scalar(x_418)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_418;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_417);
return x_423;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_367);
lean_dec(x_267);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_424 = l_Lake_loadPackageCore___closed__6;
x_425 = lean_string_append(x_1, x_424);
x_426 = lean_string_append(x_425, x_11);
lean_dec(x_11);
x_427 = lean_box(3);
x_428 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_428, 0, x_426);
x_429 = lean_unbox(x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*1, x_429);
x_430 = lean_array_get_size(x_3);
x_431 = lean_array_push(x_3, x_428);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_368);
return x_433;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_loadPackageCore___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[root]", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lake_loadPackage___closed__0;
x_6 = l_Lake_Env_leanSearchPath(x_4);
lean_dec(x_4);
x_7 = lean_st_ref_set(x_5, x_6, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_loadPackage___closed__1;
x_10 = l_Lake_loadPackageCore(x_9, x_1, x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_23 = x_11;
} else {
 lean_dec_ref(x_11);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_10, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_36 = x_11;
} else {
 lean_dec_ref(x_11);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_configFileExists___closed__0 = _init_l_Lake_configFileExists___closed__0();
lean_mark_persistent(l_Lake_configFileExists___closed__0);
l_Lake_configFileExists___closed__1 = _init_l_Lake_configFileExists___closed__1();
lean_mark_persistent(l_Lake_configFileExists___closed__1);
l_Lake_loadPackageCore___closed__0 = _init_l_Lake_loadPackageCore___closed__0();
lean_mark_persistent(l_Lake_loadPackageCore___closed__0);
l_Lake_loadPackageCore___closed__1 = _init_l_Lake_loadPackageCore___closed__1();
lean_mark_persistent(l_Lake_loadPackageCore___closed__1);
l_Lake_loadPackageCore___closed__2 = _init_l_Lake_loadPackageCore___closed__2();
lean_mark_persistent(l_Lake_loadPackageCore___closed__2);
l_Lake_loadPackageCore___closed__3 = _init_l_Lake_loadPackageCore___closed__3();
lean_mark_persistent(l_Lake_loadPackageCore___closed__3);
l_Lake_loadPackageCore___closed__4 = _init_l_Lake_loadPackageCore___closed__4();
lean_mark_persistent(l_Lake_loadPackageCore___closed__4);
l_Lake_loadPackageCore___closed__5 = _init_l_Lake_loadPackageCore___closed__5();
lean_mark_persistent(l_Lake_loadPackageCore___closed__5);
l_Lake_loadPackageCore___closed__6 = _init_l_Lake_loadPackageCore___closed__6();
lean_mark_persistent(l_Lake_loadPackageCore___closed__6);
l_Lake_loadPackage___closed__0 = _init_l_Lake_loadPackage___closed__0();
lean_mark_persistent(l_Lake_loadPackage___closed__0);
l_Lake_loadPackage___closed__1 = _init_l_Lake_loadPackage___closed__1();
lean_mark_persistent(l_Lake_loadPackage___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
