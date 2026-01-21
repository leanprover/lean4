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
static lean_object* l_Lake_loadPackageCore___closed__7;
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__3;
static lean_object* l_Lake_loadPackageCore___closed__6;
static lean_object* l_Lake_loadPackageCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object*);
static lean_object* l_Lake_loadPackage___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__8;
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_loadPackageCore___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
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
x_1 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": configuration file not found: ", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" are both present; using ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__8() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 9);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_2, 10);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 11);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 2);
x_20 = lean_ctor_get(x_2, 12);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_2, 13);
lean_inc_ref(x_21);
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
 x_22 = x_2;
} else {
 lean_dec_ref(x_2);
 x_22 = lean_box(0);
}
lean_inc_ref(x_12);
x_23 = l_System_FilePath_extension(x_12);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc_ref(x_13);
x_25 = l_Lake_resolvePath(x_13);
x_26 = lean_string_utf8_byte_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec_ref(x_13);
lean_inc_ref(x_25);
if (lean_is_scalar(x_22)) {
 x_29 = lean_alloc_ctor(0, 14, 3);
} else {
 x_29 = x_22;
}
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_6);
lean_ctor_set(x_29, 2, x_7);
lean_ctor_set(x_29, 3, x_8);
lean_ctor_set(x_29, 4, x_9);
lean_ctor_set(x_29, 5, x_10);
lean_ctor_set(x_29, 6, x_11);
lean_ctor_set(x_29, 7, x_12);
lean_ctor_set(x_29, 8, x_25);
lean_ctor_set(x_29, 9, x_14);
lean_ctor_set(x_29, 10, x_15);
lean_ctor_set(x_29, 11, x_16);
lean_ctor_set(x_29, 12, x_20);
lean_ctor_set(x_29, 13, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*14, x_17);
lean_ctor_set_uint8(x_29, sizeof(void*)*14 + 1, x_18);
lean_ctor_set_uint8(x_29, sizeof(void*)*14 + 2, x_19);
x_30 = l_Lake_configFileExists___closed__0;
x_31 = lean_string_dec_eq(x_24, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lake_configFileExists___closed__1;
x_33 = lean_string_dec_eq(x_24, x_32);
lean_dec(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_29);
x_34 = l_Lake_loadPackageCore___closed__0;
x_35 = lean_string_append(x_1, x_34);
x_36 = lean_string_append(x_35, x_25);
lean_dec_ref(x_25);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_get_size(x_3);
x_40 = lean_array_push(x_3, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_42 = l_Lake_loadTomlConfig(x_29, x_3);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; 
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_1);
x_56 = l_Lake_loadLeanConfig(x_29, x_3);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l_Lake_loadPackageCore___closed__1;
x_60 = l_Lake_loadPackageCore___closed__2;
x_61 = l_Prod_map___redArg(x_59, x_60, x_58);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = l_Lake_loadPackageCore___closed__1;
x_65 = l_Lake_loadPackageCore___closed__2;
x_66 = l_Prod_map___redArg(x_64, x_65, x_62);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
return x_56;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_56);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_72 = l_Lake_loadPackageCore___closed__3;
x_73 = lean_string_append(x_1, x_72);
x_74 = lean_string_append(x_73, x_13);
lean_dec_ref(x_13);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_get_size(x_3);
x_78 = lean_array_push(x_3, x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_23);
lean_dec_ref(x_13);
x_80 = l_Lake_configFileExists___closed__0;
lean_inc_ref(x_12);
x_81 = l_System_FilePath_addExtension(x_12, x_80);
lean_inc_ref(x_81);
lean_inc_ref(x_11);
x_82 = l_Lake_joinRelative(x_11, x_81);
lean_inc_ref(x_82);
x_83 = l_Lake_resolvePath(x_82);
x_84 = l_Lake_configFileExists___closed__1;
x_85 = l_System_FilePath_addExtension(x_12, x_84);
lean_inc_ref(x_85);
lean_inc_ref(x_11);
x_86 = l_Lake_joinRelative(x_11, x_85);
x_87 = lean_string_utf8_byte_size(x_83);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_eq(x_87, x_88);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; 
lean_dec_ref(x_82);
x_90 = l_System_FilePath_pathExists(x_86);
lean_dec_ref(x_86);
if (x_90 == 0)
{
lean_dec_ref(x_85);
lean_dec_ref(x_1);
x_91 = x_3;
goto block_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_116 = l_Lake_loadPackageCore___closed__4;
x_117 = lean_string_append(x_1, x_116);
x_118 = lean_string_append(x_117, x_81);
x_119 = l_Lake_loadPackageCore___closed__5;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_string_append(x_120, x_85);
lean_dec_ref(x_85);
x_122 = l_Lake_loadPackageCore___closed__6;
x_123 = lean_string_append(x_121, x_122);
x_124 = lean_string_append(x_123, x_81);
x_125 = 1;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_push(x_3, x_126);
x_91 = x_127;
goto block_115;
}
block_115:
{
lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_22)) {
 x_92 = lean_alloc_ctor(0, 14, 3);
} else {
 x_92 = x_22;
}
lean_ctor_set(x_92, 0, x_5);
lean_ctor_set(x_92, 1, x_6);
lean_ctor_set(x_92, 2, x_7);
lean_ctor_set(x_92, 3, x_8);
lean_ctor_set(x_92, 4, x_9);
lean_ctor_set(x_92, 5, x_10);
lean_ctor_set(x_92, 6, x_11);
lean_ctor_set(x_92, 7, x_81);
lean_ctor_set(x_92, 8, x_83);
lean_ctor_set(x_92, 9, x_14);
lean_ctor_set(x_92, 10, x_15);
lean_ctor_set(x_92, 11, x_16);
lean_ctor_set(x_92, 12, x_20);
lean_ctor_set(x_92, 13, x_21);
lean_ctor_set_uint8(x_92, sizeof(void*)*14, x_17);
lean_ctor_set_uint8(x_92, sizeof(void*)*14 + 1, x_18);
lean_ctor_set_uint8(x_92, sizeof(void*)*14 + 2, x_19);
x_93 = l_Lake_loadLeanConfig(x_92, x_91);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 1);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_95, 1, x_98);
return x_93;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_95);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_93, 0, x_102);
return x_93;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_93, 0);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_93);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_107 = x_103;
} else {
 lean_dec_ref(x_103);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_106);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
return x_110;
}
}
else
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_93);
if (x_111 == 0)
{
return x_93;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_93, 0);
x_113 = lean_ctor_get(x_93, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_93);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
lean_dec_ref(x_83);
lean_dec_ref(x_81);
lean_inc_ref(x_86);
x_128 = l_Lake_resolvePath(x_86);
x_129 = lean_string_utf8_byte_size(x_128);
x_130 = lean_nat_dec_eq(x_129, x_88);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_86);
lean_dec_ref(x_82);
lean_dec_ref(x_1);
if (lean_is_scalar(x_22)) {
 x_131 = lean_alloc_ctor(0, 14, 3);
} else {
 x_131 = x_22;
}
lean_ctor_set(x_131, 0, x_5);
lean_ctor_set(x_131, 1, x_6);
lean_ctor_set(x_131, 2, x_7);
lean_ctor_set(x_131, 3, x_8);
lean_ctor_set(x_131, 4, x_9);
lean_ctor_set(x_131, 5, x_10);
lean_ctor_set(x_131, 6, x_11);
lean_ctor_set(x_131, 7, x_85);
lean_ctor_set(x_131, 8, x_128);
lean_ctor_set(x_131, 9, x_14);
lean_ctor_set(x_131, 10, x_15);
lean_ctor_set(x_131, 11, x_16);
lean_ctor_set(x_131, 12, x_20);
lean_ctor_set(x_131, 13, x_21);
lean_ctor_set_uint8(x_131, sizeof(void*)*14, x_17);
lean_ctor_set_uint8(x_131, sizeof(void*)*14 + 1, x_18);
lean_ctor_set_uint8(x_131, sizeof(void*)*14 + 2, x_19);
x_132 = l_Lake_loadTomlConfig(x_131, x_3);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_132, 0, x_136);
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_132, 0);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_132);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_132);
if (x_142 == 0)
{
return x_132;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_132, 0);
x_144 = lean_ctor_get(x_132, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_132);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_128);
lean_dec_ref(x_85);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_146 = l_Lake_loadPackageCore___closed__7;
x_147 = lean_string_append(x_1, x_146);
x_148 = lean_string_append(x_147, x_82);
lean_dec_ref(x_82);
x_149 = l_Lake_loadPackageCore___closed__8;
x_150 = lean_string_append(x_148, x_149);
x_151 = lean_string_append(x_150, x_86);
lean_dec_ref(x_86);
x_152 = 3;
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
x_154 = lean_array_get_size(x_3);
x_155 = lean_array_push(x_3, x_153);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
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
x_1 = lean_mk_string_unchecked("[root]", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_searchPathRef;
x_6 = l_Lake_Env_leanSearchPath(x_4);
x_7 = lean_st_ref_set(x_5, x_6);
x_8 = l_Lake_loadPackage___closed__0;
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
l_Lake_loadPackageCore___closed__7 = _init_l_Lake_loadPackageCore___closed__7();
lean_mark_persistent(l_Lake_loadPackageCore___closed__7);
l_Lake_loadPackageCore___closed__8 = _init_l_Lake_loadPackageCore___closed__8();
lean_mark_persistent(l_Lake_loadPackageCore___closed__8);
l_Lake_loadPackage___closed__0 = _init_l_Lake_loadPackage___closed__0();
lean_mark_persistent(l_Lake_loadPackage___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
