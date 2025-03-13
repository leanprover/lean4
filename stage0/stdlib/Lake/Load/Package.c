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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__2;
static lean_object* l_Lake_loadPackageCore___closed__4;
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__2;
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___lambda__2___closed__1;
lean_object* l_Prod_map___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__3;
static lean_object* l_Lake_loadPackageCore___lambda__3___closed__1;
static lean_object* l_Lake_realConfigFile_realPath___closed__1;
static lean_object* l_Lake_loadPackageCore___closed__6;
static lean_object* l_Lake_loadPackageCore___closed__1;
static lean_object* l_Lake_loadPackageCore___lambda__2___closed__2;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__1(lean_object*);
static lean_object* l_Lake_configFileExists___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__2;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile_realPath(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__5;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
static lean_object* _init_l_Lake_configFileExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_configFileExists___closed__2() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Lake_configFileExists___closed__1;
lean_inc(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_Lake_configFileExists___closed__2;
x_7 = l_System_FilePath_addExtension(x_1, x_6);
x_8 = l_System_FilePath_pathExists(x_5, x_2);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_System_FilePath_pathExists(x_7, x_11);
lean_dec(x_7);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec(x_1);
return x_17;
}
}
}
static lean_object* _init_l_Lake_realConfigFile_realPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile_realPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_System_FilePath_pathExists(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = l_Lake_realConfigFile_realPath___closed__1;
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lake_realConfigFile_realPath___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
x_21 = l_Lake_realConfigFile_realPath___closed__1;
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Lake_realConfigFile_realPath___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_34; 
lean_inc(x_1);
x_34 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lake_configFileExists___closed__1;
lean_inc(x_1);
x_36 = l_System_FilePath_addExtension(x_1, x_35);
x_37 = lean_io_realpath(x_36, x_2);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_System_FilePath_pathExists(x_38, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lake_realConfigFile_realPath___closed__1;
x_3 = x_44;
x_4 = x_43;
goto block_33;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_3 = x_38;
x_4 = x_45;
goto block_33;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = l_Lake_realConfigFile_realPath___closed__1;
x_3 = x_47;
x_4 = x_46;
goto block_33;
}
}
else
{
lean_object* x_48; 
lean_dec(x_34);
x_48 = lean_io_realpath(x_1, x_2);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_System_FilePath_pathExists(x_49, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_49);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = l_Lake_realConfigFile_realPath___closed__1;
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_Lake_realConfigFile_realPath___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_51, 0);
lean_dec(x_61);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_dec(x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_48);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_48, 0);
lean_dec(x_65);
x_66 = l_Lake_realConfigFile_realPath___closed__1;
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_66);
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 1);
lean_inc(x_67);
lean_dec(x_48);
x_68 = l_Lake_realConfigFile_realPath___closed__1;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
block_33:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = l_Lake_configFileExists___closed__2;
x_10 = l_System_FilePath_addExtension(x_1, x_9);
x_11 = lean_io_realpath(x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_System_FilePath_pathExists(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l_Lake_realConfigFile_realPath___closed__1;
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lake_realConfigFile_realPath___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_11, 0);
lean_dec(x_28);
x_29 = l_Lake_realConfigFile_realPath___closed__1;
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = l_Lake_realConfigFile_realPath___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadPackageCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_4);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set(x_17, 5, x_6);
lean_ctor_set(x_17, 6, x_7);
lean_ctor_set(x_17, 7, x_8);
lean_ctor_set(x_17, 8, x_12);
lean_ctor_set(x_17, 9, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*10, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*10 + 1, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*10 + 2, x_11);
x_18 = l_Lake_loadLeanConfig(x_17, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_25 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_26 = l_Prod_map___rarg(x_24, x_25, x_23);
lean_ctor_set(x_19, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_30 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_31 = l_Prod_map___rarg(x_29, x_30, x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
x_37 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_38 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_39 = l_Prod_map___rarg(x_37, x_38, x_34);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_18, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_18, 0, x_47);
return x_18;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_dec(x_18);
x_49 = lean_ctor_get(x_19, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_51 = x_19;
} else {
 lean_dec_ref(x_19);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
return x_18;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_18, 0);
x_56 = lean_ctor_get(x_18, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_18);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lake_loadPackageCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": configuration has unsupported file extension: ", 48, 48);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_configFileExists___closed__1;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_configFileExists___closed__2;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_12 = l_Lake_realConfigFile_realPath___closed__1;
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_3);
x_17 = lean_string_append(x_16, x_12);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_6);
x_21 = lean_array_push(x_6, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lake_loadTomlConfig(x_4, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_40 = x_25;
} else {
 lean_dec_ref(x_25);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_24, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_24;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_25, 0);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_25);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_24, 0, x_50);
return x_24;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_dec(x_24);
x_52 = lean_ctor_get(x_25, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_25, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_54 = x_25;
} else {
 lean_dec_ref(x_25);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_24, 0);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_24);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lake_loadLeanConfig(x_4, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_68 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_69 = l_Prod_map___rarg(x_67, x_68, x_66);
lean_ctor_set(x_62, 0, x_69);
return x_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_62);
x_72 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_73 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_74 = l_Prod_map___rarg(x_72, x_73, x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_61, 0, x_75);
return x_61;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_dec(x_61);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
x_80 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_81 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_82 = l_Prod_map___rarg(x_80, x_81, x_77);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_61);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_61, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_62);
if (x_87 == 0)
{
return x_61;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_62, 0);
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_61, 0, x_90);
return x_61;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_61, 1);
lean_inc(x_91);
lean_dec(x_61);
x_92 = lean_ctor_get(x_62, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_62, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_94 = x_62;
} else {
 lean_dec_ref(x_62);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
return x_96;
}
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_61);
if (x_97 == 0)
{
return x_61;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_61, 0);
x_99 = lean_ctor_get(x_61, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_61);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" are both present; using ", 25, 25);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_16 = lean_ctor_get(x_2, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 9);
lean_inc(x_17);
lean_inc(x_9);
x_18 = l_System_FilePath_extension(x_9);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_20 = lean_ctor_get(x_2, 9);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 8);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 7);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 6);
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 5);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = l_Lake_configFileExists___closed__1;
lean_inc(x_9);
x_31 = l_System_FilePath_addExtension(x_9, x_30);
x_32 = l_Lake_configFileExists___closed__2;
x_33 = l_System_FilePath_addExtension(x_9, x_32);
lean_inc(x_7);
x_34 = l_System_FilePath_join(x_7, x_8);
lean_inc(x_34);
x_35 = l_System_FilePath_join(x_34, x_31);
x_36 = l_System_FilePath_join(x_34, x_33);
x_37 = l_System_FilePath_pathExists(x_35, x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_System_FilePath_pathExists(x_36, x_40);
x_42 = lean_unbox(x_39);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_31);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_33);
lean_free_object(x_2);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = l_Lake_realConfigFile_realPath___closed__1;
x_48 = lean_string_append(x_47, x_1);
x_49 = l_Lake_loadPackageCore___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_50, x_35);
lean_dec(x_35);
x_52 = l_Lake_loadPackageCore___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_36);
lean_dec(x_36);
x_55 = lean_string_append(x_54, x_47);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_3);
x_59 = lean_array_push(x_3, x_57);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_59);
lean_ctor_set(x_37, 0, x_58);
lean_ctor_set(x_41, 0, x_37);
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
lean_dec(x_41);
x_61 = l_Lake_realConfigFile_realPath___closed__1;
x_62 = lean_string_append(x_61, x_1);
x_63 = l_Lake_loadPackageCore___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_35);
lean_dec(x_35);
x_66 = l_Lake_loadPackageCore___closed__2;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_36);
lean_dec(x_36);
x_69 = lean_string_append(x_68, x_61);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_3);
x_73 = lean_array_push(x_3, x_71);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_73);
lean_ctor_set(x_37, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_37);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_36);
lean_dec(x_35);
x_75 = lean_ctor_get(x_41, 1);
lean_inc(x_75);
lean_dec(x_41);
lean_ctor_set(x_2, 4, x_33);
x_76 = l_Lake_loadTomlConfig(x_2, x_3, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_box(0);
lean_ctor_set(x_37, 1, x_82);
lean_ctor_set(x_37, 0, x_81);
lean_ctor_set(x_77, 0, x_37);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_box(0);
lean_ctor_set(x_37, 1, x_85);
lean_ctor_set(x_37, 0, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_37);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_76, 0, x_86);
return x_76;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_ctor_get(x_77, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_90 = x_77;
} else {
 lean_dec_ref(x_77);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
lean_ctor_set(x_37, 1, x_91);
lean_ctor_set(x_37, 0, x_88);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_37);
lean_ctor_set(x_92, 1, x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_free_object(x_37);
x_94 = !lean_is_exclusive(x_76);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_76, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
return x_76;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_77, 0);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_76, 0, x_99);
return x_76;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_76, 1);
lean_inc(x_100);
lean_dec(x_76);
x_101 = lean_ctor_get(x_77, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_103 = x_77;
} else {
 lean_dec_ref(x_77);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_37);
x_106 = !lean_is_exclusive(x_76);
if (x_106 == 0)
{
return x_76;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_76, 0);
x_108 = lean_ctor_get(x_76, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_76);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_object* x_110; uint8_t x_111; 
lean_free_object(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_2);
x_110 = lean_ctor_get(x_41, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_33);
x_112 = lean_ctor_get(x_41, 1);
lean_inc(x_112);
lean_dec(x_41);
x_113 = lean_box(0);
x_114 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_113, x_3, x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_115 = lean_ctor_get(x_41, 1);
lean_inc(x_115);
lean_dec(x_41);
x_116 = l_Lake_realConfigFile_realPath___closed__1;
x_117 = lean_string_append(x_116, x_1);
x_118 = l_Lake_loadPackageCore___closed__3;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_string_append(x_119, x_31);
x_121 = l_Lake_loadPackageCore___closed__4;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_string_append(x_122, x_33);
lean_dec(x_33);
x_124 = l_Lake_loadPackageCore___closed__5;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_31);
x_127 = lean_string_append(x_126, x_116);
x_128 = 1;
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_128);
x_130 = lean_array_push(x_3, x_129);
x_131 = lean_box(0);
x_132 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_131, x_130, x_115);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_37, 0);
x_134 = lean_ctor_get(x_37, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_37);
x_135 = l_System_FilePath_pathExists(x_36, x_134);
x_136 = lean_unbox(x_133);
lean_dec(x_133);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_31);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_33);
lean_free_object(x_2);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_140 = x_135;
} else {
 lean_dec_ref(x_135);
 x_140 = lean_box(0);
}
x_141 = l_Lake_realConfigFile_realPath___closed__1;
x_142 = lean_string_append(x_141, x_1);
x_143 = l_Lake_loadPackageCore___closed__1;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_35);
lean_dec(x_35);
x_146 = l_Lake_loadPackageCore___closed__2;
x_147 = lean_string_append(x_145, x_146);
x_148 = lean_string_append(x_147, x_36);
lean_dec(x_36);
x_149 = lean_string_append(x_148, x_141);
x_150 = 3;
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
x_152 = lean_array_get_size(x_3);
x_153 = lean_array_push(x_3, x_151);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_140)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_140;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_139);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_36);
lean_dec(x_35);
x_156 = lean_ctor_get(x_135, 1);
lean_inc(x_156);
lean_dec(x_135);
lean_ctor_set(x_2, 4, x_33);
x_157 = l_Lake_loadTomlConfig(x_2, x_3, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_163 = x_158;
} else {
 lean_dec_ref(x_158);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_163;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_ctor_get(x_157, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_169 = x_157;
} else {
 lean_dec_ref(x_157);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_158, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_158, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_172 = x_158;
} else {
 lean_dec_ref(x_158);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_168);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_157, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_157, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_177 = x_157;
} else {
 lean_dec_ref(x_157);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
else
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_2);
x_179 = lean_ctor_get(x_135, 0);
lean_inc(x_179);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_33);
x_181 = lean_ctor_get(x_135, 1);
lean_inc(x_181);
lean_dec(x_135);
x_182 = lean_box(0);
x_183 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_182, x_3, x_181);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_184 = lean_ctor_get(x_135, 1);
lean_inc(x_184);
lean_dec(x_135);
x_185 = l_Lake_realConfigFile_realPath___closed__1;
x_186 = lean_string_append(x_185, x_1);
x_187 = l_Lake_loadPackageCore___closed__3;
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_31);
x_190 = l_Lake_loadPackageCore___closed__4;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_string_append(x_191, x_33);
lean_dec(x_33);
x_193 = l_Lake_loadPackageCore___closed__5;
x_194 = lean_string_append(x_192, x_193);
x_195 = lean_string_append(x_194, x_31);
x_196 = lean_string_append(x_195, x_185);
x_197 = 1;
x_198 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_197);
x_199 = lean_array_push(x_3, x_198);
x_200 = lean_box(0);
x_201 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_200, x_199, x_184);
return x_201;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_dec(x_2);
x_202 = l_Lake_configFileExists___closed__1;
lean_inc(x_9);
x_203 = l_System_FilePath_addExtension(x_9, x_202);
x_204 = l_Lake_configFileExists___closed__2;
x_205 = l_System_FilePath_addExtension(x_9, x_204);
lean_inc(x_7);
x_206 = l_System_FilePath_join(x_7, x_8);
lean_inc(x_206);
x_207 = l_System_FilePath_join(x_206, x_203);
x_208 = l_System_FilePath_join(x_206, x_205);
x_209 = l_System_FilePath_pathExists(x_207, x_4);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = l_System_FilePath_pathExists(x_208, x_211);
x_214 = lean_unbox(x_210);
lean_dec(x_210);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; 
lean_dec(x_203);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = lean_unbox(x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_205);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_218 = x_213;
} else {
 lean_dec_ref(x_213);
 x_218 = lean_box(0);
}
x_219 = l_Lake_realConfigFile_realPath___closed__1;
x_220 = lean_string_append(x_219, x_1);
x_221 = l_Lake_loadPackageCore___closed__1;
x_222 = lean_string_append(x_220, x_221);
x_223 = lean_string_append(x_222, x_207);
lean_dec(x_207);
x_224 = l_Lake_loadPackageCore___closed__2;
x_225 = lean_string_append(x_223, x_224);
x_226 = lean_string_append(x_225, x_208);
lean_dec(x_208);
x_227 = lean_string_append(x_226, x_219);
x_228 = 3;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
x_230 = lean_array_get_size(x_3);
x_231 = lean_array_push(x_3, x_229);
if (lean_is_scalar(x_212)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_212;
 lean_ctor_set_tag(x_232, 1);
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
if (lean_is_scalar(x_218)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_218;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_217);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_208);
lean_dec(x_207);
x_234 = lean_ctor_get(x_213, 1);
lean_inc(x_234);
lean_dec(x_213);
x_235 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_235, 0, x_5);
lean_ctor_set(x_235, 1, x_6);
lean_ctor_set(x_235, 2, x_7);
lean_ctor_set(x_235, 3, x_8);
lean_ctor_set(x_235, 4, x_205);
lean_ctor_set(x_235, 5, x_10);
lean_ctor_set(x_235, 6, x_11);
lean_ctor_set(x_235, 7, x_12);
lean_ctor_set(x_235, 8, x_16);
lean_ctor_set(x_235, 9, x_17);
lean_ctor_set_uint8(x_235, sizeof(void*)*10, x_13);
lean_ctor_set_uint8(x_235, sizeof(void*)*10 + 1, x_14);
lean_ctor_set_uint8(x_235, sizeof(void*)*10 + 2, x_15);
x_236 = l_Lake_loadTomlConfig(x_235, x_3, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
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
if (lean_is_scalar(x_212)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_212;
}
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
lean_dec(x_212);
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
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_212);
x_254 = lean_ctor_get(x_236, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_236, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_256 = x_236;
} else {
 lean_dec_ref(x_236);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
else
{
lean_object* x_258; uint8_t x_259; 
lean_dec(x_212);
lean_dec(x_208);
lean_dec(x_207);
x_258 = lean_ctor_get(x_213, 0);
lean_inc(x_258);
x_259 = lean_unbox(x_258);
lean_dec(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_205);
x_260 = lean_ctor_get(x_213, 1);
lean_inc(x_260);
lean_dec(x_213);
x_261 = lean_box(0);
x_262 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_203, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_261, x_3, x_260);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_263 = lean_ctor_get(x_213, 1);
lean_inc(x_263);
lean_dec(x_213);
x_264 = l_Lake_realConfigFile_realPath___closed__1;
x_265 = lean_string_append(x_264, x_1);
x_266 = l_Lake_loadPackageCore___closed__3;
x_267 = lean_string_append(x_265, x_266);
x_268 = lean_string_append(x_267, x_203);
x_269 = l_Lake_loadPackageCore___closed__4;
x_270 = lean_string_append(x_268, x_269);
x_271 = lean_string_append(x_270, x_205);
lean_dec(x_205);
x_272 = l_Lake_loadPackageCore___closed__5;
x_273 = lean_string_append(x_271, x_272);
x_274 = lean_string_append(x_273, x_203);
x_275 = lean_string_append(x_274, x_264);
x_276 = 1;
x_277 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*1, x_276);
x_278 = lean_array_push(x_3, x_277);
x_279 = lean_box(0);
x_280 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_203, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_279, x_278, x_263);
return x_280;
}
}
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_281 = lean_ctor_get(x_18, 0);
lean_inc(x_281);
lean_dec(x_18);
x_282 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_283 = l_System_FilePath_join(x_282, x_9);
lean_dec(x_9);
x_284 = l_System_FilePath_pathExists(x_283, x_4);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_unbox(x_285);
lean_dec(x_285);
if (x_286 == 0)
{
uint8_t x_287; 
lean_dec(x_281);
lean_dec(x_2);
x_287 = !lean_is_exclusive(x_284);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_288 = lean_ctor_get(x_284, 0);
lean_dec(x_288);
x_289 = l_Lake_realConfigFile_realPath___closed__1;
x_290 = lean_string_append(x_289, x_1);
x_291 = l_Lake_loadPackageCore___closed__6;
x_292 = lean_string_append(x_290, x_291);
x_293 = lean_string_append(x_292, x_283);
lean_dec(x_283);
x_294 = lean_string_append(x_293, x_289);
x_295 = 3;
x_296 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set_uint8(x_296, sizeof(void*)*1, x_295);
x_297 = lean_array_get_size(x_3);
x_298 = lean_array_push(x_3, x_296);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set(x_284, 0, x_299);
return x_284;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_300 = lean_ctor_get(x_284, 1);
lean_inc(x_300);
lean_dec(x_284);
x_301 = l_Lake_realConfigFile_realPath___closed__1;
x_302 = lean_string_append(x_301, x_1);
x_303 = l_Lake_loadPackageCore___closed__6;
x_304 = lean_string_append(x_302, x_303);
x_305 = lean_string_append(x_304, x_283);
lean_dec(x_283);
x_306 = lean_string_append(x_305, x_301);
x_307 = 3;
x_308 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*1, x_307);
x_309 = lean_array_get_size(x_3);
x_310 = lean_array_push(x_3, x_308);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_300);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_284, 1);
lean_inc(x_313);
lean_dec(x_284);
x_314 = lean_box(0);
x_315 = l_Lake_loadPackageCore___lambda__3(x_281, x_1, x_283, x_2, x_314, x_3, x_313);
lean_dec(x_283);
lean_dec(x_281);
return x_315;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = lean_unbox(x_10);
lean_dec(x_10);
x_19 = lean_unbox(x_11);
lean_dec(x_11);
x_20 = l_Lake_loadPackageCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_18, x_19, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_loadPackageCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadPackageCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__2() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lake_Env_leanSearchPath(x_4);
lean_dec(x_4);
x_6 = l_Lake_loadPackage___closed__1;
x_7 = lean_st_ref_set(x_6, x_5, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_loadPackage___closed__2;
x_10 = l_Lake_loadPackageCore(x_9, x_1, x_2, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
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
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
l_Lake_configFileExists___closed__1 = _init_l_Lake_configFileExists___closed__1();
lean_mark_persistent(l_Lake_configFileExists___closed__1);
l_Lake_configFileExists___closed__2 = _init_l_Lake_configFileExists___closed__2();
lean_mark_persistent(l_Lake_configFileExists___closed__2);
l_Lake_realConfigFile_realPath___closed__1 = _init_l_Lake_realConfigFile_realPath___closed__1();
lean_mark_persistent(l_Lake_realConfigFile_realPath___closed__1);
l_Lake_loadPackageCore___lambda__2___closed__1 = _init_l_Lake_loadPackageCore___lambda__2___closed__1();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__2___closed__1);
l_Lake_loadPackageCore___lambda__2___closed__2 = _init_l_Lake_loadPackageCore___lambda__2___closed__2();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__2___closed__2);
l_Lake_loadPackageCore___lambda__3___closed__1 = _init_l_Lake_loadPackageCore___lambda__3___closed__1();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__3___closed__1);
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
l_Lake_loadPackage___closed__1 = _init_l_Lake_loadPackage___closed__1();
lean_mark_persistent(l_Lake_loadPackage___closed__1);
l_Lake_loadPackage___closed__2 = _init_l_Lake_loadPackage___closed__2();
lean_mark_persistent(l_Lake_loadPackage___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
