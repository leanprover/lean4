// Lean compiler output
// Module: Lake.Load.Package
// Imports: Lake.Load.Config Lake.Config.Package Lake.Util.IO Lake.Load.Lean Lake.Load.Toml
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
lean_object* l_Lake_Package_inputsFileIn(lean_object*, lean_object*);
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
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lake_Cache_isDisabled(lean_object*);
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
lean_object* l_Lake_CacheMap_load(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_loadInputsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_System_FilePath_pathExists(x_5, x_2);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_Lake_configFileExists___closed__1;
x_11 = l_System_FilePath_addExtension(x_1, x_10);
x_12 = l_System_FilePath_pathExists(x_11, x_9);
lean_dec_ref(x_11);
return x_12;
}
else
{
lean_dec_ref(x_1);
return x_6;
}
}
else
{
lean_object* x_13; 
lean_dec_ref(x_3);
x_13 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec_ref(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_1);
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
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_6);
x_12 = l_Lake_configFileExists___closed__1;
x_13 = l_System_FilePath_addExtension(x_1, x_12);
x_14 = l_Lake_resolvePath(x_13, x_8);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec_ref(x_3);
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
lean_inc_ref(x_1);
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
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 8);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 9);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_18 = lean_ctor_get(x_2, 10);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_2, 11);
lean_inc_ref(x_19);
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
lean_inc_ref(x_10);
x_21 = l_System_FilePath_extension(x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec_ref(x_11);
x_22 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_10);
x_23 = l_System_FilePath_addExtension(x_10, x_22);
lean_inc_ref(x_23);
lean_inc_ref(x_9);
x_24 = l_Lake_joinRelative(x_9, x_23);
lean_inc_ref(x_24);
x_25 = l_Lake_resolvePath(x_24, x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lake_configFileExists___closed__1;
x_30 = l_System_FilePath_addExtension(x_10, x_29);
lean_inc_ref(x_30);
lean_inc_ref(x_9);
x_31 = l_Lake_joinRelative(x_9, x_30);
x_32 = lean_string_utf8_byte_size(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_84; 
lean_free_object(x_25);
lean_dec_ref(x_24);
x_35 = l_System_FilePath_pathExists(x_31, x_28);
lean_dec_ref(x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_84 = lean_unbox(x_36);
lean_dec(x_36);
if (x_84 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_1);
x_38 = x_3;
goto block_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_85 = l_Lake_loadPackageCore___closed__0;
x_86 = lean_string_append(x_1, x_85);
lean_inc_ref(x_23);
x_87 = lean_string_append(x_86, x_23);
x_88 = l_Lake_loadPackageCore___closed__1;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_30);
x_91 = l_Lake_loadPackageCore___closed__2;
x_92 = lean_string_append(x_90, x_91);
lean_inc_ref(x_23);
x_93 = lean_string_append(x_92, x_23);
x_94 = 1;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_array_push(x_3, x_95);
x_38 = x_96;
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
lean_object* x_97; uint8_t x_98; 
lean_dec(x_27);
lean_dec_ref(x_23);
lean_inc_ref(x_31);
x_97 = l_Lake_resolvePath(x_31, x_28);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_string_utf8_byte_size(x_99);
x_102 = lean_nat_dec_eq(x_101, x_33);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_97);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
if (lean_is_scalar(x_20)) {
 x_103 = lean_alloc_ctor(0, 12, 3);
} else {
 x_103 = x_20;
}
lean_ctor_set(x_103, 0, x_5);
lean_ctor_set(x_103, 1, x_6);
lean_ctor_set(x_103, 2, x_7);
lean_ctor_set(x_103, 3, x_8);
lean_ctor_set(x_103, 4, x_9);
lean_ctor_set(x_103, 5, x_30);
lean_ctor_set(x_103, 6, x_99);
lean_ctor_set(x_103, 7, x_12);
lean_ctor_set(x_103, 8, x_13);
lean_ctor_set(x_103, 9, x_14);
lean_ctor_set(x_103, 10, x_18);
lean_ctor_set(x_103, 11, x_19);
lean_ctor_set_uint8(x_103, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_103, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_103, sizeof(void*)*12 + 2, x_17);
x_104 = l_Lake_loadTomlConfig(x_103, x_3, x_100);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_104, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_box(0);
lean_ctor_set(x_25, 1, x_110);
lean_ctor_set(x_25, 0, x_109);
lean_ctor_set(x_105, 0, x_25);
return x_104;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = lean_box(0);
lean_ctor_set(x_25, 1, x_113);
lean_ctor_set(x_25, 0, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_25);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_104, 0, x_114);
return x_104;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_104, 1);
lean_inc(x_115);
lean_dec(x_104);
x_116 = lean_ctor_get(x_105, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_118 = x_105;
} else {
 lean_dec_ref(x_105);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
lean_ctor_set(x_25, 1, x_119);
lean_ctor_set(x_25, 0, x_116);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_25);
lean_ctor_set(x_120, 1, x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_115);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_free_object(x_25);
x_122 = !lean_is_exclusive(x_104);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_104, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_105);
if (x_124 == 0)
{
return x_104;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_105, 0);
x_126 = lean_ctor_get(x_105, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_105);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_104, 0, x_127);
return x_104;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_104, 1);
lean_inc(x_128);
lean_dec(x_104);
x_129 = lean_ctor_get(x_105, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_105, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_131 = x_105;
} else {
 lean_dec_ref(x_105);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_99);
lean_dec_ref(x_30);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_134 = l_Lake_loadPackageCore___closed__3;
x_135 = lean_string_append(x_1, x_134);
x_136 = lean_string_append(x_135, x_24);
x_137 = l_Lake_loadPackageCore___closed__4;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_31);
x_140 = 3;
x_141 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_140);
x_142 = lean_array_get_size(x_3);
x_143 = lean_array_push(x_3, x_141);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_143);
lean_ctor_set(x_25, 0, x_142);
lean_ctor_set(x_97, 0, x_25);
return x_97;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_97, 0);
x_145 = lean_ctor_get(x_97, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_97);
x_146 = lean_string_utf8_byte_size(x_144);
x_147 = lean_nat_dec_eq(x_146, x_33);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
if (lean_is_scalar(x_20)) {
 x_148 = lean_alloc_ctor(0, 12, 3);
} else {
 x_148 = x_20;
}
lean_ctor_set(x_148, 0, x_5);
lean_ctor_set(x_148, 1, x_6);
lean_ctor_set(x_148, 2, x_7);
lean_ctor_set(x_148, 3, x_8);
lean_ctor_set(x_148, 4, x_9);
lean_ctor_set(x_148, 5, x_30);
lean_ctor_set(x_148, 6, x_144);
lean_ctor_set(x_148, 7, x_12);
lean_ctor_set(x_148, 8, x_13);
lean_ctor_set(x_148, 9, x_14);
lean_ctor_set(x_148, 10, x_18);
lean_ctor_set(x_148, 11, x_19);
lean_ctor_set_uint8(x_148, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_148, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_148, sizeof(void*)*12 + 2, x_17);
x_149 = l_Lake_loadTomlConfig(x_148, x_3, x_145);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_155 = x_150;
} else {
 lean_dec_ref(x_150);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
lean_ctor_set(x_25, 1, x_156);
lean_ctor_set(x_25, 0, x_153);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_25);
lean_ctor_set(x_157, 1, x_154);
if (lean_is_scalar(x_152)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_152;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_151);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_25);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_160 = x_149;
} else {
 lean_dec_ref(x_149);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_150, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_160;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_159);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_144);
lean_dec_ref(x_30);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_166 = l_Lake_loadPackageCore___closed__3;
x_167 = lean_string_append(x_1, x_166);
x_168 = lean_string_append(x_167, x_24);
x_169 = l_Lake_loadPackageCore___closed__4;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_string_append(x_170, x_31);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_3);
x_175 = lean_array_push(x_3, x_173);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_175);
lean_ctor_set(x_25, 0, x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_25);
lean_ctor_set(x_176, 1, x_145);
return x_176;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_177 = lean_ctor_get(x_25, 0);
x_178 = lean_ctor_get(x_25, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_25);
x_179 = l_Lake_configFileExists___closed__1;
x_180 = l_System_FilePath_addExtension(x_10, x_179);
lean_inc_ref(x_180);
lean_inc_ref(x_9);
x_181 = l_Lake_joinRelative(x_9, x_180);
x_182 = lean_string_utf8_byte_size(x_177);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_nat_dec_eq(x_182, x_183);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_212; 
lean_dec_ref(x_24);
x_185 = l_System_FilePath_pathExists(x_181, x_178);
lean_dec_ref(x_181);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec_ref(x_185);
x_212 = lean_unbox(x_186);
lean_dec(x_186);
if (x_212 == 0)
{
lean_dec_ref(x_180);
lean_dec_ref(x_1);
x_188 = x_3;
goto block_211;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_213 = l_Lake_loadPackageCore___closed__0;
x_214 = lean_string_append(x_1, x_213);
lean_inc_ref(x_23);
x_215 = lean_string_append(x_214, x_23);
x_216 = l_Lake_loadPackageCore___closed__1;
x_217 = lean_string_append(x_215, x_216);
x_218 = lean_string_append(x_217, x_180);
x_219 = l_Lake_loadPackageCore___closed__2;
x_220 = lean_string_append(x_218, x_219);
lean_inc_ref(x_23);
x_221 = lean_string_append(x_220, x_23);
x_222 = 1;
x_223 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_222);
x_224 = lean_array_push(x_3, x_223);
x_188 = x_224;
goto block_211;
}
block_211:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
if (lean_is_scalar(x_20)) {
 x_189 = lean_alloc_ctor(0, 12, 3);
} else {
 x_189 = x_20;
}
lean_ctor_set(x_189, 0, x_5);
lean_ctor_set(x_189, 1, x_6);
lean_ctor_set(x_189, 2, x_7);
lean_ctor_set(x_189, 3, x_8);
lean_ctor_set(x_189, 4, x_9);
lean_ctor_set(x_189, 5, x_23);
lean_ctor_set(x_189, 6, x_177);
lean_ctor_set(x_189, 7, x_12);
lean_ctor_set(x_189, 8, x_13);
lean_ctor_set(x_189, 9, x_14);
lean_ctor_set(x_189, 10, x_18);
lean_ctor_set(x_189, 11, x_19);
lean_ctor_set_uint8(x_189, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_189, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_189, sizeof(void*)*12 + 2, x_17);
x_190 = l_Lake_loadLeanConfig(x_189, x_188, x_187);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_194 = x_190;
} else {
 lean_dec_ref(x_190);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_196 = x_191;
} else {
 lean_dec_ref(x_191);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_198);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
if (lean_is_scalar(x_196)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_196;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_195);
if (lean_is_scalar(x_194)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_194;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_193);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_190, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_205 = x_190;
} else {
 lean_dec_ref(x_190);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_191, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_191, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_208 = x_191;
} else {
 lean_dec_ref(x_191);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
if (lean_is_scalar(x_205)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_205;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_204);
return x_210;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_177);
lean_dec_ref(x_23);
lean_inc_ref(x_181);
x_225 = l_Lake_resolvePath(x_181, x_178);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = lean_string_utf8_byte_size(x_226);
x_230 = lean_nat_dec_eq(x_229, x_183);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_228);
lean_dec_ref(x_181);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
if (lean_is_scalar(x_20)) {
 x_231 = lean_alloc_ctor(0, 12, 3);
} else {
 x_231 = x_20;
}
lean_ctor_set(x_231, 0, x_5);
lean_ctor_set(x_231, 1, x_6);
lean_ctor_set(x_231, 2, x_7);
lean_ctor_set(x_231, 3, x_8);
lean_ctor_set(x_231, 4, x_9);
lean_ctor_set(x_231, 5, x_180);
lean_ctor_set(x_231, 6, x_226);
lean_ctor_set(x_231, 7, x_12);
lean_ctor_set(x_231, 8, x_13);
lean_ctor_set(x_231, 9, x_14);
lean_ctor_set(x_231, 10, x_18);
lean_ctor_set(x_231, 11, x_19);
lean_ctor_set_uint8(x_231, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_231, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_231, sizeof(void*)*12 + 2, x_17);
x_232 = l_Lake_loadTomlConfig(x_231, x_3, x_227);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
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
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_236);
lean_ctor_set(x_240, 1, x_239);
if (lean_is_scalar(x_238)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_238;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_237);
if (lean_is_scalar(x_235)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_235;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_234);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_243 = lean_ctor_get(x_232, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_244 = x_232;
} else {
 lean_dec_ref(x_232);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_233, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_233, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_247 = x_233;
} else {
 lean_dec_ref(x_233);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
if (lean_is_scalar(x_244)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_244;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_243);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_226);
lean_dec_ref(x_180);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_250 = l_Lake_loadPackageCore___closed__3;
x_251 = lean_string_append(x_1, x_250);
x_252 = lean_string_append(x_251, x_24);
x_253 = l_Lake_loadPackageCore___closed__4;
x_254 = lean_string_append(x_252, x_253);
x_255 = lean_string_append(x_254, x_181);
x_256 = 3;
x_257 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set_uint8(x_257, sizeof(void*)*1, x_256);
x_258 = lean_array_get_size(x_3);
x_259 = lean_array_push(x_3, x_257);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_228)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_228;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_227);
return x_261;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_21, 0);
lean_inc(x_262);
lean_dec_ref(x_21);
lean_inc_ref(x_11);
x_263 = l_Lake_resolvePath(x_11, x_4);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_ctor_get(x_263, 1);
x_267 = lean_string_utf8_byte_size(x_265);
x_268 = lean_unsigned_to_nat(0u);
x_269 = lean_nat_dec_eq(x_267, x_268);
lean_dec(x_267);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec_ref(x_11);
lean_inc(x_265);
if (lean_is_scalar(x_20)) {
 x_270 = lean_alloc_ctor(0, 12, 3);
} else {
 x_270 = x_20;
}
lean_ctor_set(x_270, 0, x_5);
lean_ctor_set(x_270, 1, x_6);
lean_ctor_set(x_270, 2, x_7);
lean_ctor_set(x_270, 3, x_8);
lean_ctor_set(x_270, 4, x_9);
lean_ctor_set(x_270, 5, x_10);
lean_ctor_set(x_270, 6, x_265);
lean_ctor_set(x_270, 7, x_12);
lean_ctor_set(x_270, 8, x_13);
lean_ctor_set(x_270, 9, x_14);
lean_ctor_set(x_270, 10, x_18);
lean_ctor_set(x_270, 11, x_19);
lean_ctor_set_uint8(x_270, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_270, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_270, sizeof(void*)*12 + 2, x_17);
x_271 = l_Lake_configFileExists___closed__0;
x_272 = lean_string_dec_eq(x_262, x_271);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = l_Lake_configFileExists___closed__1;
x_274 = lean_string_dec_eq(x_262, x_273);
lean_dec(x_262);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec_ref(x_270);
x_275 = l_Lake_loadPackageCore___closed__5;
x_276 = lean_string_append(x_1, x_275);
x_277 = lean_string_append(x_276, x_265);
x_278 = 3;
x_279 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*1, x_278);
x_280 = lean_array_get_size(x_3);
x_281 = lean_array_push(x_3, x_279);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
lean_ctor_set(x_263, 0, x_282);
return x_263;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_free_object(x_263);
lean_dec(x_265);
lean_dec_ref(x_1);
x_283 = l_Lake_loadTomlConfig(x_270, x_3, x_266);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_283, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_284);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_284, 0);
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set(x_284, 0, x_290);
return x_283;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_284, 0);
x_292 = lean_ctor_get(x_284, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_284);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
lean_ctor_set(x_283, 0, x_295);
return x_283;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_296 = lean_ctor_get(x_283, 1);
lean_inc(x_296);
lean_dec(x_283);
x_297 = lean_ctor_get(x_284, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_284, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_299 = x_284;
} else {
 lean_dec_ref(x_284);
 x_299 = lean_box(0);
}
x_300 = lean_box(0);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_300);
if (lean_is_scalar(x_299)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_299;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_298);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_296);
return x_303;
}
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_283);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_283, 0);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_284);
if (x_306 == 0)
{
return x_283;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_284, 0);
x_308 = lean_ctor_get(x_284, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_284);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set(x_283, 0, x_309);
return x_283;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_283, 1);
lean_inc(x_310);
lean_dec(x_283);
x_311 = lean_ctor_get(x_284, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_284, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_313 = x_284;
} else {
 lean_dec_ref(x_284);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_310);
return x_315;
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_free_object(x_263);
lean_dec(x_265);
lean_dec(x_262);
lean_dec_ref(x_1);
x_316 = l_Lake_loadLeanConfig(x_270, x_3, x_266);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_316);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_316, 0);
lean_dec(x_319);
x_320 = !lean_is_exclusive(x_317);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_317, 0);
x_322 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_323 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_324 = l_Prod_map___redArg(x_323, x_322, x_321);
lean_ctor_set(x_317, 0, x_324);
return x_316;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_325 = lean_ctor_get(x_317, 0);
x_326 = lean_ctor_get(x_317, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_317);
x_327 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_328 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_329 = l_Prod_map___redArg(x_328, x_327, x_325);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_326);
lean_ctor_set(x_316, 0, x_330);
return x_316;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_331 = lean_ctor_get(x_316, 1);
lean_inc(x_331);
lean_dec(x_316);
x_332 = lean_ctor_get(x_317, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_317, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_334 = x_317;
} else {
 lean_dec_ref(x_317);
 x_334 = lean_box(0);
}
x_335 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_336 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_337 = l_Prod_map___redArg(x_336, x_335, x_332);
if (lean_is_scalar(x_334)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_334;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_333);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
return x_339;
}
}
else
{
uint8_t x_340; 
x_340 = !lean_is_exclusive(x_316);
if (x_340 == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = lean_ctor_get(x_316, 0);
lean_dec(x_341);
x_342 = !lean_is_exclusive(x_317);
if (x_342 == 0)
{
return x_316;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_317, 0);
x_344 = lean_ctor_get(x_317, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_317);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_316, 0, x_345);
return x_316;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_346 = lean_ctor_get(x_316, 1);
lean_inc(x_346);
lean_dec(x_316);
x_347 = lean_ctor_get(x_317, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_317, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_349 = x_317;
} else {
 lean_dec_ref(x_317);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_346);
return x_351;
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_265);
lean_dec(x_262);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_352 = l_Lake_loadPackageCore___closed__6;
x_353 = lean_string_append(x_1, x_352);
x_354 = lean_string_append(x_353, x_11);
x_355 = 3;
x_356 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set_uint8(x_356, sizeof(void*)*1, x_355);
x_357 = lean_array_get_size(x_3);
x_358 = lean_array_push(x_3, x_356);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
lean_ctor_set(x_263, 0, x_359);
return x_263;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_360 = lean_ctor_get(x_263, 0);
x_361 = lean_ctor_get(x_263, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_263);
x_362 = lean_string_utf8_byte_size(x_360);
x_363 = lean_unsigned_to_nat(0u);
x_364 = lean_nat_dec_eq(x_362, x_363);
lean_dec(x_362);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
lean_dec_ref(x_11);
lean_inc(x_360);
if (lean_is_scalar(x_20)) {
 x_365 = lean_alloc_ctor(0, 12, 3);
} else {
 x_365 = x_20;
}
lean_ctor_set(x_365, 0, x_5);
lean_ctor_set(x_365, 1, x_6);
lean_ctor_set(x_365, 2, x_7);
lean_ctor_set(x_365, 3, x_8);
lean_ctor_set(x_365, 4, x_9);
lean_ctor_set(x_365, 5, x_10);
lean_ctor_set(x_365, 6, x_360);
lean_ctor_set(x_365, 7, x_12);
lean_ctor_set(x_365, 8, x_13);
lean_ctor_set(x_365, 9, x_14);
lean_ctor_set(x_365, 10, x_18);
lean_ctor_set(x_365, 11, x_19);
lean_ctor_set_uint8(x_365, sizeof(void*)*12, x_15);
lean_ctor_set_uint8(x_365, sizeof(void*)*12 + 1, x_16);
lean_ctor_set_uint8(x_365, sizeof(void*)*12 + 2, x_17);
x_366 = l_Lake_configFileExists___closed__0;
x_367 = lean_string_dec_eq(x_262, x_366);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; 
x_368 = l_Lake_configFileExists___closed__1;
x_369 = lean_string_dec_eq(x_262, x_368);
lean_dec(x_262);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec_ref(x_365);
x_370 = l_Lake_loadPackageCore___closed__5;
x_371 = lean_string_append(x_1, x_370);
x_372 = lean_string_append(x_371, x_360);
x_373 = 3;
x_374 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_373);
x_375 = lean_array_get_size(x_3);
x_376 = lean_array_push(x_3, x_374);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_361);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_360);
lean_dec_ref(x_1);
x_379 = l_Lake_loadTomlConfig(x_365, x_3, x_361);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_382 = x_379;
} else {
 lean_dec_ref(x_379);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_380, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_380, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_385 = x_380;
} else {
 lean_dec_ref(x_380);
 x_385 = lean_box(0);
}
x_386 = lean_box(0);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_383);
lean_ctor_set(x_387, 1, x_386);
if (lean_is_scalar(x_385)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_385;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_384);
if (lean_is_scalar(x_382)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_382;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_381);
return x_389;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_379, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_391 = x_379;
} else {
 lean_dec_ref(x_379);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_380, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_380, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_394 = x_380;
} else {
 lean_dec_ref(x_380);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
if (lean_is_scalar(x_391)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_391;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_390);
return x_396;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_360);
lean_dec(x_262);
lean_dec_ref(x_1);
x_397 = l_Lake_loadLeanConfig(x_365, x_3, x_361);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_398, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_398, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_403 = x_398;
} else {
 lean_dec_ref(x_398);
 x_403 = lean_box(0);
}
x_404 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_405 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_406 = l_Prod_map___redArg(x_405, x_404, x_401);
if (lean_is_scalar(x_403)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_403;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_402);
if (lean_is_scalar(x_400)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_400;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_399);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_409 = lean_ctor_get(x_397, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_410 = x_397;
} else {
 lean_dec_ref(x_397);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_398, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_398, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_413 = x_398;
} else {
 lean_dec_ref(x_398);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
if (lean_is_scalar(x_410)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_410;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_409);
return x_415;
}
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_360);
lean_dec(x_262);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_416 = l_Lake_loadPackageCore___closed__6;
x_417 = lean_string_append(x_1, x_416);
x_418 = lean_string_append(x_417, x_11);
x_419 = 3;
x_420 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*1, x_419);
x_421 = lean_array_get_size(x_3);
x_422 = lean_array_push(x_3, x_420);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_361);
return x_424;
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
lean_dec_ref(x_1);
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
x_5 = l_Lake_loadPackage___closed__0;
x_6 = l_Lake_Env_leanSearchPath(x_4);
x_7 = lean_st_ref_set(x_5, x_6, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
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
LEAN_EXPORT lean_object* l_Lake_Package_loadInputsFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_113; uint8_t x_114; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 1);
x_9 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_113 = l_Lake_Cache_isDisabled(x_9);
if (x_113 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_2, 3);
x_117 = lean_ctor_get(x_116, 25);
if (lean_obj_tag(x_117) == 0)
{
x_114 = x_8;
goto block_115;
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
x_119 = lean_unbox(x_118);
x_114 = x_119;
goto block_115;
}
}
else
{
x_10 = x_113;
goto block_112;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_112:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_2);
x_11 = l_Lake_Package_inputsFileIn(x_9, x_2);
x_12 = l_Lake_CacheMap_load(x_11, x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_st_mk_ref(x_16, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_2, 19);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_2, 19, x_22);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_ctor_get(x_2, 5);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_ctor_get(x_2, 7);
x_32 = lean_ctor_get(x_2, 8);
x_33 = lean_ctor_get(x_2, 9);
x_34 = lean_ctor_get(x_2, 10);
x_35 = lean_ctor_get(x_2, 11);
x_36 = lean_ctor_get(x_2, 12);
x_37 = lean_ctor_get(x_2, 13);
x_38 = lean_ctor_get(x_2, 14);
x_39 = lean_ctor_get(x_2, 15);
x_40 = lean_ctor_get(x_2, 16);
x_41 = lean_ctor_get(x_2, 17);
x_42 = lean_ctor_get(x_2, 18);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_23);
x_44 = lean_alloc_ctor(0, 20, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_44, 3, x_27);
lean_ctor_set(x_44, 4, x_28);
lean_ctor_set(x_44, 5, x_29);
lean_ctor_set(x_44, 6, x_30);
lean_ctor_set(x_44, 7, x_31);
lean_ctor_set(x_44, 8, x_32);
lean_ctor_set(x_44, 9, x_33);
lean_ctor_set(x_44, 10, x_34);
lean_ctor_set(x_44, 11, x_35);
lean_ctor_set(x_44, 12, x_36);
lean_ctor_set(x_44, 13, x_37);
lean_ctor_set(x_44, 14, x_38);
lean_ctor_set(x_44, 15, x_39);
lean_ctor_set(x_44, 16, x_40);
lean_ctor_set(x_44, 17, x_41);
lean_ctor_set(x_44, 18, x_42);
lean_ctor_set(x_44, 19, x_43);
lean_ctor_set(x_13, 0, x_44);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_2, 9);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_2, 10);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_2, 11);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 12);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_2, 13);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 14);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_2, 15);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_2, 16);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_2, 17);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_2, 18);
lean_inc_ref(x_65);
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
 lean_ctor_release(x_2, 13);
 lean_ctor_release(x_2, 14);
 lean_ctor_release(x_2, 15);
 lean_ctor_release(x_2, 16);
 lean_ctor_release(x_2, 17);
 lean_ctor_release(x_2, 18);
 lean_ctor_release(x_2, 19);
 x_66 = x_2;
} else {
 lean_dec_ref(x_2);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_45);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 20, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_50);
lean_ctor_set(x_68, 4, x_51);
lean_ctor_set(x_68, 5, x_52);
lean_ctor_set(x_68, 6, x_53);
lean_ctor_set(x_68, 7, x_54);
lean_ctor_set(x_68, 8, x_55);
lean_ctor_set(x_68, 9, x_56);
lean_ctor_set(x_68, 10, x_57);
lean_ctor_set(x_68, 11, x_58);
lean_ctor_set(x_68, 12, x_59);
lean_ctor_set(x_68, 13, x_60);
lean_ctor_set(x_68, 14, x_61);
lean_ctor_set(x_68, 15, x_62);
lean_ctor_set(x_68, 16, x_63);
lean_ctor_set(x_68, 17, x_64);
lean_ctor_set(x_68, 18, x_65);
lean_ctor_set(x_68, 19, x_67);
lean_ctor_set(x_13, 0, x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_13);
lean_ctor_set(x_69, 1, x_46);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_70 = lean_ctor_get(x_13, 0);
x_71 = lean_ctor_get(x_13, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_13);
x_72 = lean_st_mk_ref(x_70, x_14);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_2, 9);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_2, 10);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_2, 11);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 12);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_2, 13);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 14);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_2, 15);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_2, 16);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_2, 17);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_2, 18);
lean_inc_ref(x_94);
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
 lean_ctor_release(x_2, 13);
 lean_ctor_release(x_2, 14);
 lean_ctor_release(x_2, 15);
 lean_ctor_release(x_2, 16);
 lean_ctor_release(x_2, 17);
 lean_ctor_release(x_2, 18);
 lean_ctor_release(x_2, 19);
 x_95 = x_2;
} else {
 lean_dec_ref(x_2);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_73);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 20, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_76);
lean_ctor_set(x_97, 1, x_77);
lean_ctor_set(x_97, 2, x_78);
lean_ctor_set(x_97, 3, x_79);
lean_ctor_set(x_97, 4, x_80);
lean_ctor_set(x_97, 5, x_81);
lean_ctor_set(x_97, 6, x_82);
lean_ctor_set(x_97, 7, x_83);
lean_ctor_set(x_97, 8, x_84);
lean_ctor_set(x_97, 9, x_85);
lean_ctor_set(x_97, 10, x_86);
lean_ctor_set(x_97, 11, x_87);
lean_ctor_set(x_97, 12, x_88);
lean_ctor_set(x_97, 13, x_89);
lean_ctor_set(x_97, 14, x_90);
lean_ctor_set(x_97, 15, x_91);
lean_ctor_set(x_97, 16, x_92);
lean_ctor_set(x_97, 17, x_93);
lean_ctor_set(x_97, 18, x_94);
lean_ctor_set(x_97, 19, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_71);
if (lean_is_scalar(x_75)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_75;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_74);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_2);
x_100 = !lean_is_exclusive(x_12);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_12, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_13);
if (x_102 == 0)
{
return x_12;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_13, 0);
x_104 = lean_ctor_get(x_13, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_13);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_12, 0, x_105);
return x_12;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_12, 1);
lean_inc(x_106);
lean_dec(x_12);
x_107 = lean_ctor_get(x_13, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_13, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_109 = x_13;
} else {
 lean_dec_ref(x_13);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
else
{
lean_dec_ref(x_9);
goto block_7;
}
}
block_115:
{
if (x_114 == 0)
{
lean_dec_ref(x_9);
goto block_7;
}
else
{
x_10 = x_113;
goto block_112;
}
}
}
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
