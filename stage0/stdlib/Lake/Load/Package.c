// Lean compiler output
// Module: Lake.Load.Package
// Imports: public import Lake.Load.Config public import Lake.Config.Package import Lake.Util.IO import Lake.Load.Lean import Lake.Load.Toml
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
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__0;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__0;
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__3;
static lean_object* l_Lake_loadPackageCore___closed__6;
static lean_object* l_Lake_loadPackageCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object*);
static lean_object* l_Lake_loadPackage___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__1;
static lean_object* l_Lake_configFileExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__5;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_System_FilePath_pathExists(x_5);
lean_dec_ref(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lake_configFileExists___closed__1;
x_8 = l_System_FilePath_addExtension(x_1, x_7);
x_9 = l_System_FilePath_pathExists(x_8);
lean_dec_ref(x_8);
return x_9;
}
else
{
lean_dec_ref(x_1);
return x_6;
}
}
else
{
uint8_t x_10; 
lean_dec_ref(x_3);
x_10 = l_System_FilePath_pathExists(x_1);
lean_dec_ref(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_configFileExists(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_Lake_resolvePath(x_5);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_6);
x_10 = l_Lake_configFileExists___closed__1;
x_11 = l_System_FilePath_addExtension(x_1, x_10);
x_12 = l_Lake_resolvePath(x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec_ref(x_3);
x_13 = l_Lake_resolvePath(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_realConfigFile(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": configuration has unsupported file extension: ", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": configuration file not found: ", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" are both present; using ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 9);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 10);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 2);
x_19 = lean_ctor_get(x_2, 11);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_2, 12);
lean_inc_ref(x_20);
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
 lean_ctor_release(x_2, 12);
 x_21 = x_2;
} else {
 lean_dec_ref(x_2);
 x_21 = lean_box(0);
}
lean_inc_ref(x_11);
x_22 = l_System_FilePath_extension(x_11);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_12);
x_24 = l_Lake_resolvePath(x_12);
x_25 = lean_string_utf8_byte_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec_ref(x_12);
lean_inc_ref(x_24);
if (lean_is_scalar(x_21)) {
 x_28 = lean_alloc_ctor(0, 13, 3);
} else {
 x_28 = x_21;
}
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_7);
lean_ctor_set(x_28, 3, x_8);
lean_ctor_set(x_28, 4, x_9);
lean_ctor_set(x_28, 5, x_10);
lean_ctor_set(x_28, 6, x_11);
lean_ctor_set(x_28, 7, x_24);
lean_ctor_set(x_28, 8, x_13);
lean_ctor_set(x_28, 9, x_14);
lean_ctor_set(x_28, 10, x_15);
lean_ctor_set(x_28, 11, x_19);
lean_ctor_set(x_28, 12, x_20);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 2, x_18);
x_29 = l_Lake_configFileExists___closed__0;
x_30 = lean_string_dec_eq(x_23, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lake_configFileExists___closed__1;
x_32 = lean_string_dec_eq(x_23, x_31);
lean_dec(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_28);
x_33 = l_Lake_loadPackageCore___closed__0;
x_34 = lean_string_append(x_1, x_33);
x_35 = lean_string_append(x_34, x_24);
lean_dec_ref(x_24);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_3);
x_39 = lean_array_push(x_3, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_41 = l_Lake_loadTomlConfig(x_28, x_3);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; 
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_1);
x_55 = l_Lake_loadLeanConfig(x_28, x_3);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0___boxed), 1, 0);
x_59 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1), 1, 0);
x_60 = l_Prod_map___redArg(x_58, x_59, x_57);
lean_ctor_set(x_55, 0, x_60);
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0___boxed), 1, 0);
x_64 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1), 1, 0);
x_65 = l_Prod_map___redArg(x_63, x_64, x_61);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_55);
if (x_67 == 0)
{
return x_55;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_55, 0);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_55);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_71 = l_Lake_loadPackageCore___closed__1;
x_72 = lean_string_append(x_1, x_71);
x_73 = lean_string_append(x_72, x_12);
lean_dec_ref(x_12);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_get_size(x_3);
x_77 = lean_array_push(x_3, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_22);
lean_dec_ref(x_12);
x_79 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_11);
x_80 = l_System_FilePath_addExtension(x_11, x_79);
lean_inc_ref(x_80);
lean_inc_ref(x_10);
x_81 = l_Lake_joinRelative(x_10, x_80);
lean_inc_ref(x_81);
x_82 = l_Lake_resolvePath(x_81);
x_83 = l_Lake_configFileExists___closed__1;
x_84 = l_System_FilePath_addExtension(x_11, x_83);
lean_inc_ref(x_84);
lean_inc_ref(x_10);
x_85 = l_Lake_joinRelative(x_10, x_84);
x_86 = lean_string_utf8_byte_size(x_82);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_eq(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; 
lean_dec_ref(x_81);
x_89 = l_System_FilePath_pathExists(x_85);
lean_dec_ref(x_85);
if (x_89 == 0)
{
lean_dec_ref(x_84);
lean_dec_ref(x_1);
x_90 = x_3;
goto block_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_115 = l_Lake_loadPackageCore___closed__2;
x_116 = lean_string_append(x_1, x_115);
x_117 = lean_string_append(x_116, x_80);
x_118 = l_Lake_loadPackageCore___closed__3;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_string_append(x_119, x_84);
lean_dec_ref(x_84);
x_121 = l_Lake_loadPackageCore___closed__4;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_string_append(x_122, x_80);
x_124 = 1;
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_124);
x_126 = lean_array_push(x_3, x_125);
x_90 = x_126;
goto block_114;
}
block_114:
{
lean_object* x_91; lean_object* x_92; 
if (lean_is_scalar(x_21)) {
 x_91 = lean_alloc_ctor(0, 13, 3);
} else {
 x_91 = x_21;
}
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_6);
lean_ctor_set(x_91, 2, x_7);
lean_ctor_set(x_91, 3, x_8);
lean_ctor_set(x_91, 4, x_9);
lean_ctor_set(x_91, 5, x_10);
lean_ctor_set(x_91, 6, x_80);
lean_ctor_set(x_91, 7, x_82);
lean_ctor_set(x_91, 8, x_13);
lean_ctor_set(x_91, 9, x_14);
lean_ctor_set(x_91, 10, x_15);
lean_ctor_set(x_91, 11, x_19);
lean_ctor_set(x_91, 12, x_20);
lean_ctor_set_uint8(x_91, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_91, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_91, sizeof(void*)*13 + 2, x_18);
x_92 = l_Lake_loadLeanConfig(x_91, x_90);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 1);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_94, 1, x_97);
return x_92;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_92, 0, x_101);
return x_92;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_92, 0);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_92);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_105);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
return x_109;
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_92);
if (x_110 == 0)
{
return x_92;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_92);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec_ref(x_82);
lean_dec_ref(x_80);
lean_inc_ref(x_85);
x_127 = l_Lake_resolvePath(x_85);
x_128 = lean_string_utf8_byte_size(x_127);
x_129 = lean_nat_dec_eq(x_128, x_87);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_85);
lean_dec_ref(x_81);
lean_dec_ref(x_1);
if (lean_is_scalar(x_21)) {
 x_130 = lean_alloc_ctor(0, 13, 3);
} else {
 x_130 = x_21;
}
lean_ctor_set(x_130, 0, x_5);
lean_ctor_set(x_130, 1, x_6);
lean_ctor_set(x_130, 2, x_7);
lean_ctor_set(x_130, 3, x_8);
lean_ctor_set(x_130, 4, x_9);
lean_ctor_set(x_130, 5, x_10);
lean_ctor_set(x_130, 6, x_84);
lean_ctor_set(x_130, 7, x_127);
lean_ctor_set(x_130, 8, x_13);
lean_ctor_set(x_130, 9, x_14);
lean_ctor_set(x_130, 10, x_15);
lean_ctor_set(x_130, 11, x_19);
lean_ctor_set(x_130, 12, x_20);
lean_ctor_set_uint8(x_130, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_130, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_130, sizeof(void*)*13 + 2, x_18);
x_131 = l_Lake_loadTomlConfig(x_130, x_3);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_131, 0, x_135);
return x_131;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_131, 0);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_131);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_131);
if (x_141 == 0)
{
return x_131;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_131, 0);
x_143 = lean_ctor_get(x_131, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_131);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_127);
lean_dec_ref(x_84);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_145 = l_Lake_loadPackageCore___closed__5;
x_146 = lean_string_append(x_1, x_145);
x_147 = lean_string_append(x_146, x_81);
lean_dec_ref(x_81);
x_148 = l_Lake_loadPackageCore___closed__6;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_string_append(x_149, x_85);
lean_dec_ref(x_85);
x_151 = 3;
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_151);
x_153 = lean_array_get_size(x_3);
x_154 = lean_array_push(x_3, x_152);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_loadPackageCore___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadPackageCore(x_1, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lake_loadPackage___closed__0;
x_6 = l_Lake_Env_leanSearchPath(x_4);
x_7 = lean_st_ref_set(x_5, x_6);
x_8 = l_Lake_loadPackage___closed__1;
x_9 = l_Lake_loadPackageCore(x_8, x_1, x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadPackage(x_1, x_2);
return x_4;
}
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean(uint8_t builtin);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin);
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
