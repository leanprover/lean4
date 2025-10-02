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
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec_ref(x_12);
x_23 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_11);
x_24 = l_System_FilePath_addExtension(x_11, x_23);
lean_inc_ref(x_10);
x_25 = l_Lake_joinRelative(x_10, x_24);
lean_inc_ref(x_25);
x_26 = l_Lake_resolvePath(x_25, x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lake_configFileExists___closed__1;
x_31 = l_System_FilePath_addExtension(x_11, x_30);
lean_inc_ref(x_10);
x_32 = l_Lake_joinRelative(x_10, x_31);
x_33 = lean_string_utf8_byte_size(x_28);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_85; 
lean_free_object(x_26);
lean_dec_ref(x_25);
x_36 = l_System_FilePath_pathExists(x_32, x_29);
lean_dec_ref(x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_85 = lean_unbox(x_37);
lean_dec(x_37);
if (x_85 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_1);
x_39 = x_3;
goto block_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_86 = l_Lake_loadPackageCore___closed__0;
x_87 = lean_string_append(x_1, x_86);
x_88 = lean_string_append(x_87, x_24);
x_89 = l_Lake_loadPackageCore___closed__1;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_string_append(x_90, x_31);
lean_dec_ref(x_31);
x_92 = l_Lake_loadPackageCore___closed__2;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_string_append(x_93, x_24);
x_95 = 1;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_array_push(x_3, x_96);
x_39 = x_97;
goto block_84;
}
block_84:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
if (lean_is_scalar(x_21)) {
 x_40 = lean_alloc_ctor(0, 13, 3);
} else {
 x_40 = x_21;
}
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_6);
lean_ctor_set(x_40, 2, x_7);
lean_ctor_set(x_40, 3, x_8);
lean_ctor_set(x_40, 4, x_9);
lean_ctor_set(x_40, 5, x_10);
lean_ctor_set(x_40, 6, x_24);
lean_ctor_set(x_40, 7, x_28);
lean_ctor_set(x_40, 8, x_13);
lean_ctor_set(x_40, 9, x_14);
lean_ctor_set(x_40, 10, x_15);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 2, x_18);
x_41 = l_Lake_loadLeanConfig(x_40, x_39, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_43, 1);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_43, 1, x_50);
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_42, 0, x_54);
return x_41;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_58 = x_43;
} else {
 lean_dec_ref(x_43);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_41, 0, x_61);
return x_41;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
lean_dec(x_41);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_64 = x_42;
} else {
 lean_dec_ref(x_42);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_43, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_67 = x_43;
} else {
 lean_dec_ref(x_43);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_66);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_41);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_41, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
return x_41;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_42, 0);
x_76 = lean_ctor_get(x_42, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_42);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_41, 0, x_77);
return x_41;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_41, 1);
lean_inc(x_78);
lean_dec(x_41);
x_79 = lean_ctor_get(x_42, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_42, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_81 = x_42;
} else {
 lean_dec_ref(x_42);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
}
}
}
else
{
lean_object* x_98; uint8_t x_99; 
lean_dec(x_28);
lean_dec_ref(x_24);
lean_inc_ref(x_32);
x_98 = l_Lake_resolvePath(x_32, x_29);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = lean_string_utf8_byte_size(x_100);
x_103 = lean_nat_dec_eq(x_102, x_34);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_98);
lean_dec_ref(x_32);
lean_dec_ref(x_25);
lean_dec_ref(x_1);
if (lean_is_scalar(x_21)) {
 x_104 = lean_alloc_ctor(0, 13, 3);
} else {
 x_104 = x_21;
}
lean_ctor_set(x_104, 0, x_5);
lean_ctor_set(x_104, 1, x_6);
lean_ctor_set(x_104, 2, x_7);
lean_ctor_set(x_104, 3, x_8);
lean_ctor_set(x_104, 4, x_9);
lean_ctor_set(x_104, 5, x_10);
lean_ctor_set(x_104, 6, x_31);
lean_ctor_set(x_104, 7, x_100);
lean_ctor_set(x_104, 8, x_13);
lean_ctor_set(x_104, 9, x_14);
lean_ctor_set(x_104, 10, x_15);
lean_ctor_set(x_104, 11, x_19);
lean_ctor_set(x_104, 12, x_20);
lean_ctor_set_uint8(x_104, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_104, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_104, sizeof(void*)*13 + 2, x_18);
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
lean_ctor_set(x_26, 1, x_111);
lean_ctor_set(x_26, 0, x_110);
lean_ctor_set(x_106, 0, x_26);
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
lean_ctor_set(x_26, 1, x_114);
lean_ctor_set(x_26, 0, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_26);
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
lean_ctor_set(x_26, 1, x_120);
lean_ctor_set(x_26, 0, x_117);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_26);
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
lean_free_object(x_26);
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
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_100);
lean_dec_ref(x_31);
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
x_135 = l_Lake_loadPackageCore___closed__3;
x_136 = lean_string_append(x_1, x_135);
x_137 = lean_string_append(x_136, x_25);
lean_dec_ref(x_25);
x_138 = l_Lake_loadPackageCore___closed__4;
x_139 = lean_string_append(x_137, x_138);
x_140 = lean_string_append(x_139, x_32);
lean_dec_ref(x_32);
x_141 = 3;
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_141);
x_143 = lean_array_get_size(x_3);
x_144 = lean_array_push(x_3, x_142);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_144);
lean_ctor_set(x_26, 0, x_143);
lean_ctor_set(x_98, 0, x_26);
return x_98;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_98, 0);
x_146 = lean_ctor_get(x_98, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_98);
x_147 = lean_string_utf8_byte_size(x_145);
x_148 = lean_nat_dec_eq(x_147, x_34);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_32);
lean_dec_ref(x_25);
lean_dec_ref(x_1);
if (lean_is_scalar(x_21)) {
 x_149 = lean_alloc_ctor(0, 13, 3);
} else {
 x_149 = x_21;
}
lean_ctor_set(x_149, 0, x_5);
lean_ctor_set(x_149, 1, x_6);
lean_ctor_set(x_149, 2, x_7);
lean_ctor_set(x_149, 3, x_8);
lean_ctor_set(x_149, 4, x_9);
lean_ctor_set(x_149, 5, x_10);
lean_ctor_set(x_149, 6, x_31);
lean_ctor_set(x_149, 7, x_145);
lean_ctor_set(x_149, 8, x_13);
lean_ctor_set(x_149, 9, x_14);
lean_ctor_set(x_149, 10, x_15);
lean_ctor_set(x_149, 11, x_19);
lean_ctor_set(x_149, 12, x_20);
lean_ctor_set_uint8(x_149, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_149, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_149, sizeof(void*)*13 + 2, x_18);
x_150 = l_Lake_loadTomlConfig(x_149, x_3, x_146);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
x_157 = lean_box(0);
lean_ctor_set(x_26, 1, x_157);
lean_ctor_set(x_26, 0, x_154);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_26);
lean_ctor_set(x_158, 1, x_155);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_free_object(x_26);
x_160 = lean_ctor_get(x_150, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_161 = x_150;
} else {
 lean_dec_ref(x_150);
 x_161 = lean_box(0);
}
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
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
if (lean_is_scalar(x_161)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_161;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_160);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_145);
lean_dec_ref(x_31);
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
x_167 = l_Lake_loadPackageCore___closed__3;
x_168 = lean_string_append(x_1, x_167);
x_169 = lean_string_append(x_168, x_25);
lean_dec_ref(x_25);
x_170 = l_Lake_loadPackageCore___closed__4;
x_171 = lean_string_append(x_169, x_170);
x_172 = lean_string_append(x_171, x_32);
lean_dec_ref(x_32);
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_array_get_size(x_3);
x_176 = lean_array_push(x_3, x_174);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_176);
lean_ctor_set(x_26, 0, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_26);
lean_ctor_set(x_177, 1, x_146);
return x_177;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_178 = lean_ctor_get(x_26, 0);
x_179 = lean_ctor_get(x_26, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_26);
x_180 = l_Lake_configFileExists___closed__1;
x_181 = l_System_FilePath_addExtension(x_11, x_180);
lean_inc_ref(x_10);
x_182 = l_Lake_joinRelative(x_10, x_181);
x_183 = lean_string_utf8_byte_size(x_178);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_dec_eq(x_183, x_184);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_213; 
lean_dec_ref(x_25);
x_186 = l_System_FilePath_pathExists(x_182, x_179);
lean_dec_ref(x_182);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec_ref(x_186);
x_213 = lean_unbox(x_187);
lean_dec(x_187);
if (x_213 == 0)
{
lean_dec_ref(x_181);
lean_dec_ref(x_1);
x_189 = x_3;
goto block_212;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; 
x_214 = l_Lake_loadPackageCore___closed__0;
x_215 = lean_string_append(x_1, x_214);
x_216 = lean_string_append(x_215, x_24);
x_217 = l_Lake_loadPackageCore___closed__1;
x_218 = lean_string_append(x_216, x_217);
x_219 = lean_string_append(x_218, x_181);
lean_dec_ref(x_181);
x_220 = l_Lake_loadPackageCore___closed__2;
x_221 = lean_string_append(x_219, x_220);
x_222 = lean_string_append(x_221, x_24);
x_223 = 1;
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_223);
x_225 = lean_array_push(x_3, x_224);
x_189 = x_225;
goto block_212;
}
block_212:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
if (lean_is_scalar(x_21)) {
 x_190 = lean_alloc_ctor(0, 13, 3);
} else {
 x_190 = x_21;
}
lean_ctor_set(x_190, 0, x_5);
lean_ctor_set(x_190, 1, x_6);
lean_ctor_set(x_190, 2, x_7);
lean_ctor_set(x_190, 3, x_8);
lean_ctor_set(x_190, 4, x_9);
lean_ctor_set(x_190, 5, x_10);
lean_ctor_set(x_190, 6, x_24);
lean_ctor_set(x_190, 7, x_178);
lean_ctor_set(x_190, 8, x_13);
lean_ctor_set(x_190, 9, x_14);
lean_ctor_set(x_190, 10, x_15);
lean_ctor_set(x_190, 11, x_19);
lean_ctor_set(x_190, 12, x_20);
lean_ctor_set_uint8(x_190, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_190, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_190, sizeof(void*)*13 + 2, x_18);
x_191 = l_Lake_loadLeanConfig(x_190, x_189, x_188);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_195 = x_191;
} else {
 lean_dec_ref(x_191);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_197 = x_192;
} else {
 lean_dec_ref(x_192);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_200 = x_193;
} else {
 lean_dec_ref(x_193);
 x_200 = lean_box(0);
}
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_199);
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_201);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_196);
if (lean_is_scalar(x_195)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_195;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_194);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_205 = lean_ctor_get(x_191, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_206 = x_191;
} else {
 lean_dec_ref(x_191);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_192, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_192, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_209 = x_192;
} else {
 lean_dec_ref(x_192);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
if (lean_is_scalar(x_206)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_206;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_205);
return x_211;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_178);
lean_dec_ref(x_24);
lean_inc_ref(x_182);
x_226 = l_Lake_resolvePath(x_182, x_179);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
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
x_230 = lean_string_utf8_byte_size(x_227);
x_231 = lean_nat_dec_eq(x_230, x_184);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_229);
lean_dec_ref(x_182);
lean_dec_ref(x_25);
lean_dec_ref(x_1);
if (lean_is_scalar(x_21)) {
 x_232 = lean_alloc_ctor(0, 13, 3);
} else {
 x_232 = x_21;
}
lean_ctor_set(x_232, 0, x_5);
lean_ctor_set(x_232, 1, x_6);
lean_ctor_set(x_232, 2, x_7);
lean_ctor_set(x_232, 3, x_8);
lean_ctor_set(x_232, 4, x_9);
lean_ctor_set(x_232, 5, x_10);
lean_ctor_set(x_232, 6, x_181);
lean_ctor_set(x_232, 7, x_227);
lean_ctor_set(x_232, 8, x_13);
lean_ctor_set(x_232, 9, x_14);
lean_ctor_set(x_232, 10, x_15);
lean_ctor_set(x_232, 11, x_19);
lean_ctor_set(x_232, 12, x_20);
lean_ctor_set_uint8(x_232, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_232, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_232, sizeof(void*)*13 + 2, x_18);
x_233 = l_Lake_loadTomlConfig(x_232, x_3, x_228);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_239 = x_234;
} else {
 lean_dec_ref(x_234);
 x_239 = lean_box(0);
}
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_239;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
if (lean_is_scalar(x_236)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_236;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_235);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_233, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_245 = x_233;
} else {
 lean_dec_ref(x_233);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_234, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_234, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_248 = x_234;
} else {
 lean_dec_ref(x_234);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
if (lean_is_scalar(x_245)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_245;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_244);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_227);
lean_dec_ref(x_181);
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
x_251 = l_Lake_loadPackageCore___closed__3;
x_252 = lean_string_append(x_1, x_251);
x_253 = lean_string_append(x_252, x_25);
lean_dec_ref(x_25);
x_254 = l_Lake_loadPackageCore___closed__4;
x_255 = lean_string_append(x_253, x_254);
x_256 = lean_string_append(x_255, x_182);
lean_dec_ref(x_182);
x_257 = 3;
x_258 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set_uint8(x_258, sizeof(void*)*1, x_257);
x_259 = lean_array_get_size(x_3);
x_260 = lean_array_push(x_3, x_258);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
if (lean_is_scalar(x_229)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_229;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_228);
return x_262;
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_22, 0);
lean_inc(x_263);
lean_dec_ref(x_22);
lean_inc_ref(x_12);
x_264 = l_Lake_resolvePath(x_12, x_4);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
x_268 = lean_string_utf8_byte_size(x_266);
x_269 = lean_unsigned_to_nat(0u);
x_270 = lean_nat_dec_eq(x_268, x_269);
lean_dec(x_268);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
lean_dec_ref(x_12);
lean_inc(x_266);
if (lean_is_scalar(x_21)) {
 x_271 = lean_alloc_ctor(0, 13, 3);
} else {
 x_271 = x_21;
}
lean_ctor_set(x_271, 0, x_5);
lean_ctor_set(x_271, 1, x_6);
lean_ctor_set(x_271, 2, x_7);
lean_ctor_set(x_271, 3, x_8);
lean_ctor_set(x_271, 4, x_9);
lean_ctor_set(x_271, 5, x_10);
lean_ctor_set(x_271, 6, x_11);
lean_ctor_set(x_271, 7, x_266);
lean_ctor_set(x_271, 8, x_13);
lean_ctor_set(x_271, 9, x_14);
lean_ctor_set(x_271, 10, x_15);
lean_ctor_set(x_271, 11, x_19);
lean_ctor_set(x_271, 12, x_20);
lean_ctor_set_uint8(x_271, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_271, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_271, sizeof(void*)*13 + 2, x_18);
x_272 = l_Lake_configFileExists___closed__0;
x_273 = lean_string_dec_eq(x_263, x_272);
if (x_273 == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = l_Lake_configFileExists___closed__1;
x_275 = lean_string_dec_eq(x_263, x_274);
lean_dec(x_263);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec_ref(x_271);
x_276 = l_Lake_loadPackageCore___closed__5;
x_277 = lean_string_append(x_1, x_276);
x_278 = lean_string_append(x_277, x_266);
lean_dec(x_266);
x_279 = 3;
x_280 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set_uint8(x_280, sizeof(void*)*1, x_279);
x_281 = lean_array_get_size(x_3);
x_282 = lean_array_push(x_3, x_280);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_264, 0, x_283);
return x_264;
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_free_object(x_264);
lean_dec(x_266);
lean_dec_ref(x_1);
x_284 = l_Lake_loadTomlConfig(x_271, x_3, x_267);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_284);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_ctor_get(x_284, 0);
lean_dec(x_287);
x_288 = !lean_is_exclusive(x_285);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_285, 0);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_285, 0, x_291);
return x_284;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_285, 0);
x_293 = lean_ctor_get(x_285, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_285);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_284, 0, x_296);
return x_284;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_284, 1);
lean_inc(x_297);
lean_dec(x_284);
x_298 = lean_ctor_get(x_285, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_285, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_300 = x_285;
} else {
 lean_dec_ref(x_285);
 x_300 = lean_box(0);
}
x_301 = lean_box(0);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_301);
if (lean_is_scalar(x_300)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_300;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_299);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_297);
return x_304;
}
}
else
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_284);
if (x_305 == 0)
{
lean_object* x_306; uint8_t x_307; 
x_306 = lean_ctor_get(x_284, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_285);
if (x_307 == 0)
{
return x_284;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_285, 0);
x_309 = lean_ctor_get(x_285, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_285);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
lean_ctor_set(x_284, 0, x_310);
return x_284;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_311 = lean_ctor_get(x_284, 1);
lean_inc(x_311);
lean_dec(x_284);
x_312 = lean_ctor_get(x_285, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_285, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_314 = x_285;
} else {
 lean_dec_ref(x_285);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_311);
return x_316;
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_free_object(x_264);
lean_dec(x_266);
lean_dec(x_263);
lean_dec_ref(x_1);
x_317 = l_Lake_loadLeanConfig(x_271, x_3, x_267);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
if (lean_obj_tag(x_318) == 0)
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_317);
if (x_319 == 0)
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_ctor_get(x_317, 0);
lean_dec(x_320);
x_321 = !lean_is_exclusive(x_318);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_318, 0);
x_323 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_324 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_325 = l_Prod_map___redArg(x_324, x_323, x_322);
lean_ctor_set(x_318, 0, x_325);
return x_317;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_326 = lean_ctor_get(x_318, 0);
x_327 = lean_ctor_get(x_318, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_318);
x_328 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_329 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_330 = l_Prod_map___redArg(x_329, x_328, x_326);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_327);
lean_ctor_set(x_317, 0, x_331);
return x_317;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_332 = lean_ctor_get(x_317, 1);
lean_inc(x_332);
lean_dec(x_317);
x_333 = lean_ctor_get(x_318, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_318, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_335 = x_318;
} else {
 lean_dec_ref(x_318);
 x_335 = lean_box(0);
}
x_336 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_337 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_338 = l_Prod_map___redArg(x_337, x_336, x_333);
if (lean_is_scalar(x_335)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_335;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_334);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_317);
if (x_341 == 0)
{
lean_object* x_342; uint8_t x_343; 
x_342 = lean_ctor_get(x_317, 0);
lean_dec(x_342);
x_343 = !lean_is_exclusive(x_318);
if (x_343 == 0)
{
return x_317;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_318, 0);
x_345 = lean_ctor_get(x_318, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_318);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set(x_317, 0, x_346);
return x_317;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_347 = lean_ctor_get(x_317, 1);
lean_inc(x_347);
lean_dec(x_317);
x_348 = lean_ctor_get(x_318, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_318, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_350 = x_318;
} else {
 lean_dec_ref(x_318);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_347);
return x_352;
}
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_266);
lean_dec(x_263);
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
x_353 = l_Lake_loadPackageCore___closed__6;
x_354 = lean_string_append(x_1, x_353);
x_355 = lean_string_append(x_354, x_12);
lean_dec_ref(x_12);
x_356 = 3;
x_357 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*1, x_356);
x_358 = lean_array_get_size(x_3);
x_359 = lean_array_push(x_3, x_357);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_264, 0, x_360);
return x_264;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_361 = lean_ctor_get(x_264, 0);
x_362 = lean_ctor_get(x_264, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_264);
x_363 = lean_string_utf8_byte_size(x_361);
x_364 = lean_unsigned_to_nat(0u);
x_365 = lean_nat_dec_eq(x_363, x_364);
lean_dec(x_363);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec_ref(x_12);
lean_inc(x_361);
if (lean_is_scalar(x_21)) {
 x_366 = lean_alloc_ctor(0, 13, 3);
} else {
 x_366 = x_21;
}
lean_ctor_set(x_366, 0, x_5);
lean_ctor_set(x_366, 1, x_6);
lean_ctor_set(x_366, 2, x_7);
lean_ctor_set(x_366, 3, x_8);
lean_ctor_set(x_366, 4, x_9);
lean_ctor_set(x_366, 5, x_10);
lean_ctor_set(x_366, 6, x_11);
lean_ctor_set(x_366, 7, x_361);
lean_ctor_set(x_366, 8, x_13);
lean_ctor_set(x_366, 9, x_14);
lean_ctor_set(x_366, 10, x_15);
lean_ctor_set(x_366, 11, x_19);
lean_ctor_set(x_366, 12, x_20);
lean_ctor_set_uint8(x_366, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_366, sizeof(void*)*13 + 1, x_17);
lean_ctor_set_uint8(x_366, sizeof(void*)*13 + 2, x_18);
x_367 = l_Lake_configFileExists___closed__0;
x_368 = lean_string_dec_eq(x_263, x_367);
if (x_368 == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = l_Lake_configFileExists___closed__1;
x_370 = lean_string_dec_eq(x_263, x_369);
lean_dec(x_263);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_366);
x_371 = l_Lake_loadPackageCore___closed__5;
x_372 = lean_string_append(x_1, x_371);
x_373 = lean_string_append(x_372, x_361);
lean_dec(x_361);
x_374 = 3;
x_375 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set_uint8(x_375, sizeof(void*)*1, x_374);
x_376 = lean_array_get_size(x_3);
x_377 = lean_array_push(x_3, x_375);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_362);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_361);
lean_dec_ref(x_1);
x_380 = l_Lake_loadTomlConfig(x_366, x_3, x_362);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_381, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_381, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_386 = x_381;
} else {
 lean_dec_ref(x_381);
 x_386 = lean_box(0);
}
x_387 = lean_box(0);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_384);
lean_ctor_set(x_388, 1, x_387);
if (lean_is_scalar(x_386)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_386;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_385);
if (lean_is_scalar(x_383)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_383;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_382);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_391 = lean_ctor_get(x_380, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_392 = x_380;
} else {
 lean_dec_ref(x_380);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_381, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_381, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_395 = x_381;
} else {
 lean_dec_ref(x_381);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
if (lean_is_scalar(x_392)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_392;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_391);
return x_397;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_361);
lean_dec(x_263);
lean_dec_ref(x_1);
x_398 = l_Lake_loadLeanConfig(x_366, x_3, x_362);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_399, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_399, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_404 = x_399;
} else {
 lean_dec_ref(x_399);
 x_404 = lean_box(0);
}
x_405 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_406 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_407 = l_Prod_map___redArg(x_406, x_405, x_402);
if (lean_is_scalar(x_404)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_404;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_403);
if (lean_is_scalar(x_401)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_401;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_400);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_410 = lean_ctor_get(x_398, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_411 = x_398;
} else {
 lean_dec_ref(x_398);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_399, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_399, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_414 = x_399;
} else {
 lean_dec_ref(x_399);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_413);
if (lean_is_scalar(x_411)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_411;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_410);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_361);
lean_dec(x_263);
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
x_417 = l_Lake_loadPackageCore___closed__6;
x_418 = lean_string_append(x_1, x_417);
x_419 = lean_string_append(x_418, x_12);
lean_dec_ref(x_12);
x_420 = 3;
x_421 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set_uint8(x_421, sizeof(void*)*1, x_420);
x_422 = lean_array_get_size(x_3);
x_423 = lean_array_push(x_3, x_421);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_362);
return x_425;
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
