// Lean compiler output
// Module: Lake.Load.Package
// Imports: Init Lake.Load.Lean Lake.Load.Toml
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackageCore___lambda__3___closed__2;
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
static lean_object* l_Lake_loadPackageCore___closed__3;
static lean_object* l_Lake_loadPackageCore___lambda__3___closed__1;
static lean_object* l_Lake_loadPackageCore___closed__6;
static lean_object* l_Lake_loadPackageCore___closed__1;
static lean_object* l_Lake_loadPackageCore___lambda__2___closed__2;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__1(lean_object*);
static lean_object* l_Lake_configFileExists___closed__1;
extern lean_object* l_Lean_searchPathRef;
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__2;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__5;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set(x_13, 5, x_6);
lean_ctor_set(x_13, 6, x_8);
lean_ctor_set(x_13, 7, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*8, x_7);
x_14 = l_Lake_loadLeanConfig(x_13, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_21 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_22 = l_Prod_map___rarg(x_20, x_21, x_19);
lean_ctor_set(x_15, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_26 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_27 = l_Prod_map___rarg(x_25, x_26, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
x_33 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_34 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_35 = l_Prod_map___rarg(x_33, x_34, x_30);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_14, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_14, 0, x_43);
return x_14;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_dec(x_14);
x_45 = lean_ctor_get(x_15, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_47 = x_15;
} else {
 lean_dec_ref(x_15);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Lake_loadPackageCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackageCore___lambda__3___closed__2() {
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
x_12 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lake_loadPackageCore___lambda__3___closed__2;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_12 = lean_ctor_get(x_2, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 7);
lean_inc(x_13);
lean_inc(x_8);
x_14 = l_System_FilePath_extension(x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_2, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = l_Lake_configFileExists___closed__1;
lean_inc(x_8);
x_25 = l_System_FilePath_addExtension(x_8, x_24);
x_26 = l_Lake_configFileExists___closed__2;
x_27 = l_System_FilePath_addExtension(x_8, x_26);
lean_inc(x_6);
x_28 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_28);
x_29 = l_System_FilePath_join(x_28, x_25);
x_30 = l_System_FilePath_join(x_28, x_27);
x_31 = l_System_FilePath_pathExists(x_29, x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_System_FilePath_pathExists(x_30, x_34);
x_36 = lean_unbox(x_33);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_25);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_27);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_35, 0);
lean_dec(x_40);
x_41 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_42 = lean_string_append(x_41, x_1);
x_43 = l_Lake_loadPackageCore___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_29);
lean_dec(x_29);
x_46 = l_Lake_loadPackageCore___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_string_append(x_47, x_30);
lean_dec(x_30);
x_49 = lean_string_append(x_48, x_41);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_get_size(x_3);
x_53 = lean_array_push(x_3, x_51);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_53);
lean_ctor_set(x_31, 0, x_52);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
x_55 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_56 = lean_string_append(x_55, x_1);
x_57 = l_Lake_loadPackageCore___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_29);
lean_dec(x_29);
x_60 = l_Lake_loadPackageCore___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_30);
lean_dec(x_30);
x_63 = lean_string_append(x_62, x_55);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_3);
x_67 = lean_array_push(x_3, x_65);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_67);
lean_ctor_set(x_31, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_31);
lean_ctor_set(x_68, 1, x_54);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_30);
lean_dec(x_29);
x_69 = lean_ctor_get(x_35, 1);
lean_inc(x_69);
lean_dec(x_35);
lean_ctor_set(x_2, 3, x_27);
x_70 = l_Lake_loadTomlConfig(x_2, x_3, x_69);
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
x_76 = lean_box(0);
lean_ctor_set(x_31, 1, x_76);
lean_ctor_set(x_31, 0, x_75);
lean_ctor_set(x_71, 0, x_31);
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
x_79 = lean_box(0);
lean_ctor_set(x_31, 1, x_79);
lean_ctor_set(x_31, 0, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_31);
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
x_85 = lean_box(0);
lean_ctor_set(x_31, 1, x_85);
lean_ctor_set(x_31, 0, x_82);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_31);
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
lean_free_object(x_31);
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
lean_free_object(x_31);
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
lean_object* x_104; uint8_t x_105; 
lean_free_object(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_2);
x_104 = lean_ctor_get(x_35, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_27);
x_106 = lean_ctor_get(x_35, 1);
lean_inc(x_106);
lean_dec(x_35);
x_107 = lean_box(0);
x_108 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_25, x_9, x_10, x_11, x_12, x_13, x_107, x_3, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_109 = lean_ctor_get(x_35, 1);
lean_inc(x_109);
lean_dec(x_35);
x_110 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_111 = lean_string_append(x_110, x_1);
x_112 = l_Lake_loadPackageCore___closed__3;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_25);
x_115 = l_Lake_loadPackageCore___closed__4;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_string_append(x_116, x_27);
lean_dec(x_27);
x_118 = l_Lake_loadPackageCore___closed__5;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_string_append(x_119, x_25);
x_121 = lean_string_append(x_120, x_110);
x_122 = 1;
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_122);
x_124 = lean_array_push(x_3, x_123);
x_125 = lean_box(0);
x_126 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_25, x_9, x_10, x_11, x_12, x_13, x_125, x_124, x_109);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_31, 0);
x_128 = lean_ctor_get(x_31, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_31);
x_129 = l_System_FilePath_pathExists(x_30, x_128);
x_130 = lean_unbox(x_127);
lean_dec(x_127);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
lean_dec(x_25);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_27);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
x_135 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_136 = lean_string_append(x_135, x_1);
x_137 = l_Lake_loadPackageCore___closed__1;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_29);
lean_dec(x_29);
x_140 = l_Lake_loadPackageCore___closed__2;
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_string_append(x_141, x_30);
lean_dec(x_30);
x_143 = lean_string_append(x_142, x_135);
x_144 = 3;
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
x_146 = lean_array_get_size(x_3);
x_147 = lean_array_push(x_3, x_145);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_134)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_134;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_133);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_30);
lean_dec(x_29);
x_150 = lean_ctor_get(x_129, 1);
lean_inc(x_150);
lean_dec(x_129);
lean_ctor_set(x_2, 3, x_27);
x_151 = l_Lake_loadTomlConfig(x_2, x_3, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
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
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_154;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_151, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_163 = x_151;
} else {
 lean_dec_ref(x_151);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_152, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_166 = x_152;
} else {
 lean_dec_ref(x_152);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_151, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_151, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_171 = x_151;
} else {
 lean_dec_ref(x_151);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
lean_object* x_173; uint8_t x_174; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_2);
x_173 = lean_ctor_get(x_129, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_27);
x_175 = lean_ctor_get(x_129, 1);
lean_inc(x_175);
lean_dec(x_129);
x_176 = lean_box(0);
x_177 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_25, x_9, x_10, x_11, x_12, x_13, x_176, x_3, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_178 = lean_ctor_get(x_129, 1);
lean_inc(x_178);
lean_dec(x_129);
x_179 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_180 = lean_string_append(x_179, x_1);
x_181 = l_Lake_loadPackageCore___closed__3;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_string_append(x_182, x_25);
x_184 = l_Lake_loadPackageCore___closed__4;
x_185 = lean_string_append(x_183, x_184);
x_186 = lean_string_append(x_185, x_27);
lean_dec(x_27);
x_187 = l_Lake_loadPackageCore___closed__5;
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_25);
x_190 = lean_string_append(x_189, x_179);
x_191 = 1;
x_192 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_191);
x_193 = lean_array_push(x_3, x_192);
x_194 = lean_box(0);
x_195 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_25, x_9, x_10, x_11, x_12, x_13, x_194, x_193, x_178);
return x_195;
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_2);
x_196 = l_Lake_configFileExists___closed__1;
lean_inc(x_8);
x_197 = l_System_FilePath_addExtension(x_8, x_196);
x_198 = l_Lake_configFileExists___closed__2;
x_199 = l_System_FilePath_addExtension(x_8, x_198);
lean_inc(x_6);
x_200 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_200);
x_201 = l_System_FilePath_join(x_200, x_197);
x_202 = l_System_FilePath_join(x_200, x_199);
x_203 = l_System_FilePath_pathExists(x_201, x_4);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = l_System_FilePath_pathExists(x_202, x_205);
x_208 = lean_unbox(x_204);
lean_dec(x_204);
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
lean_dec(x_197);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_199);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_212 = x_207;
} else {
 lean_dec_ref(x_207);
 x_212 = lean_box(0);
}
x_213 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_214 = lean_string_append(x_213, x_1);
x_215 = l_Lake_loadPackageCore___closed__1;
x_216 = lean_string_append(x_214, x_215);
x_217 = lean_string_append(x_216, x_201);
lean_dec(x_201);
x_218 = l_Lake_loadPackageCore___closed__2;
x_219 = lean_string_append(x_217, x_218);
x_220 = lean_string_append(x_219, x_202);
lean_dec(x_202);
x_221 = lean_string_append(x_220, x_213);
x_222 = 3;
x_223 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_222);
x_224 = lean_array_get_size(x_3);
x_225 = lean_array_push(x_3, x_223);
if (lean_is_scalar(x_206)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_206;
 lean_ctor_set_tag(x_226, 1);
}
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
if (lean_is_scalar(x_212)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_212;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_211);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_202);
lean_dec(x_201);
x_228 = lean_ctor_get(x_207, 1);
lean_inc(x_228);
lean_dec(x_207);
x_229 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_229, 0, x_5);
lean_ctor_set(x_229, 1, x_6);
lean_ctor_set(x_229, 2, x_7);
lean_ctor_set(x_229, 3, x_199);
lean_ctor_set(x_229, 4, x_9);
lean_ctor_set(x_229, 5, x_10);
lean_ctor_set(x_229, 6, x_12);
lean_ctor_set(x_229, 7, x_13);
lean_ctor_set_uint8(x_229, sizeof(void*)*8, x_11);
x_230 = l_Lake_loadTomlConfig(x_229, x_3, x_228);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_236 = x_231;
} else {
 lean_dec_ref(x_231);
 x_236 = lean_box(0);
}
x_237 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_206;
}
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_237);
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_235);
if (lean_is_scalar(x_233)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_233;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_232);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_206);
x_241 = lean_ctor_get(x_230, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_242 = x_230;
} else {
 lean_dec_ref(x_230);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_231, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_231, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_245 = x_231;
} else {
 lean_dec_ref(x_231);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_241);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_206);
x_248 = lean_ctor_get(x_230, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_230, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_250 = x_230;
} else {
 lean_dec_ref(x_230);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
}
else
{
lean_object* x_252; uint8_t x_253; 
lean_dec(x_206);
lean_dec(x_202);
lean_dec(x_201);
x_252 = lean_ctor_get(x_207, 0);
lean_inc(x_252);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_199);
x_254 = lean_ctor_get(x_207, 1);
lean_inc(x_254);
lean_dec(x_207);
x_255 = lean_box(0);
x_256 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_197, x_9, x_10, x_11, x_12, x_13, x_255, x_3, x_254);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_257 = lean_ctor_get(x_207, 1);
lean_inc(x_257);
lean_dec(x_207);
x_258 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_259 = lean_string_append(x_258, x_1);
x_260 = l_Lake_loadPackageCore___closed__3;
x_261 = lean_string_append(x_259, x_260);
x_262 = lean_string_append(x_261, x_197);
x_263 = l_Lake_loadPackageCore___closed__4;
x_264 = lean_string_append(x_262, x_263);
x_265 = lean_string_append(x_264, x_199);
lean_dec(x_199);
x_266 = l_Lake_loadPackageCore___closed__5;
x_267 = lean_string_append(x_265, x_266);
x_268 = lean_string_append(x_267, x_197);
x_269 = lean_string_append(x_268, x_258);
x_270 = 1;
x_271 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_270);
x_272 = lean_array_push(x_3, x_271);
x_273 = lean_box(0);
x_274 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_197, x_9, x_10, x_11, x_12, x_13, x_273, x_272, x_257);
return x_274;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_275 = lean_ctor_get(x_14, 0);
lean_inc(x_275);
lean_dec(x_14);
x_276 = l_System_FilePath_join(x_6, x_7);
lean_dec(x_7);
x_277 = l_System_FilePath_join(x_276, x_8);
lean_dec(x_8);
x_278 = l_System_FilePath_pathExists(x_277, x_4);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
uint8_t x_281; 
lean_dec(x_275);
lean_dec(x_2);
x_281 = !lean_is_exclusive(x_278);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_282 = lean_ctor_get(x_278, 0);
lean_dec(x_282);
x_283 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_284 = lean_string_append(x_283, x_1);
x_285 = l_Lake_loadPackageCore___closed__6;
x_286 = lean_string_append(x_284, x_285);
x_287 = lean_string_append(x_286, x_277);
lean_dec(x_277);
x_288 = lean_string_append(x_287, x_283);
x_289 = 3;
x_290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_289);
x_291 = lean_array_get_size(x_3);
x_292 = lean_array_push(x_3, x_290);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_278, 0, x_293);
return x_278;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_294 = lean_ctor_get(x_278, 1);
lean_inc(x_294);
lean_dec(x_278);
x_295 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_296 = lean_string_append(x_295, x_1);
x_297 = l_Lake_loadPackageCore___closed__6;
x_298 = lean_string_append(x_296, x_297);
x_299 = lean_string_append(x_298, x_277);
lean_dec(x_277);
x_300 = lean_string_append(x_299, x_295);
x_301 = 3;
x_302 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*1, x_301);
x_303 = lean_array_get_size(x_3);
x_304 = lean_array_push(x_3, x_302);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_294);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_278, 1);
lean_inc(x_307);
lean_dec(x_278);
x_308 = lean_box(0);
x_309 = l_Lake_loadPackageCore___lambda__3(x_275, x_1, x_277, x_2, x_308, x_3, x_307);
lean_dec(x_277);
lean_dec(x_275);
return x_309;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lake_loadPackageCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
return x_14;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lake_loadPackageCore___lambda__2___closed__1 = _init_l_Lake_loadPackageCore___lambda__2___closed__1();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__2___closed__1);
l_Lake_loadPackageCore___lambda__2___closed__2 = _init_l_Lake_loadPackageCore___lambda__2___closed__2();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__2___closed__2);
l_Lake_loadPackageCore___lambda__3___closed__1 = _init_l_Lake_loadPackageCore___lambda__3___closed__1();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__3___closed__1);
l_Lake_loadPackageCore___lambda__3___closed__2 = _init_l_Lake_loadPackageCore___lambda__3___closed__2();
lean_mark_persistent(l_Lake_loadPackageCore___lambda__3___closed__2);
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
