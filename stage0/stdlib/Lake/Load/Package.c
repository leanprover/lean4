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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_4);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set(x_16, 5, x_6);
lean_ctor_set(x_16, 6, x_7);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*9 + 1, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*9 + 2, x_10);
x_17 = l_Lake_loadLeanConfig(x_16, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_24 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_25 = l_Prod_map___rarg(x_23, x_24, x_22);
lean_ctor_set(x_18, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_29 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_30 = l_Prod_map___rarg(x_28, x_29, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
x_36 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_37 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_38 = l_Prod_map___rarg(x_36, x_37, x_33);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_17, 0, x_46);
return x_17;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_dec(x_17);
x_48 = lean_ctor_get(x_18, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*9 + 1);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*9 + 2);
x_15 = lean_ctor_get(x_2, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 8);
lean_inc(x_16);
lean_inc(x_9);
x_17 = l_System_FilePath_extension(x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_19 = lean_ctor_get(x_2, 8);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 7);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 6);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 5);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 0);
lean_dec(x_27);
x_28 = l_Lake_configFileExists___closed__1;
lean_inc(x_9);
x_29 = l_System_FilePath_addExtension(x_9, x_28);
x_30 = l_Lake_configFileExists___closed__2;
x_31 = l_System_FilePath_addExtension(x_9, x_30);
lean_inc(x_7);
x_32 = l_System_FilePath_join(x_7, x_8);
lean_inc(x_32);
x_33 = l_System_FilePath_join(x_32, x_29);
x_34 = l_System_FilePath_join(x_32, x_31);
x_35 = l_System_FilePath_pathExists(x_33, x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_System_FilePath_pathExists(x_34, x_38);
x_40 = lean_unbox(x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_29);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_31);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
x_45 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_46 = lean_string_append(x_45, x_1);
x_47 = l_Lake_loadPackageCore___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_33);
lean_dec(x_33);
x_50 = l_Lake_loadPackageCore___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_34);
lean_dec(x_34);
x_53 = lean_string_append(x_52, x_45);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_3);
x_57 = lean_array_push(x_3, x_55);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_56);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_dec(x_39);
x_59 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_60 = lean_string_append(x_59, x_1);
x_61 = l_Lake_loadPackageCore___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_33);
lean_dec(x_33);
x_64 = l_Lake_loadPackageCore___closed__2;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_string_append(x_65, x_34);
lean_dec(x_34);
x_67 = lean_string_append(x_66, x_59);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_get_size(x_3);
x_71 = lean_array_push(x_3, x_69);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_71);
lean_ctor_set(x_35, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_35);
lean_ctor_set(x_72, 1, x_58);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_34);
lean_dec(x_33);
x_73 = lean_ctor_get(x_39, 1);
lean_inc(x_73);
lean_dec(x_39);
lean_ctor_set(x_2, 4, x_31);
x_74 = l_Lake_loadTomlConfig(x_2, x_3, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_box(0);
lean_ctor_set(x_35, 1, x_80);
lean_ctor_set(x_35, 0, x_79);
lean_ctor_set(x_75, 0, x_35);
return x_74;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_75);
x_83 = lean_box(0);
lean_ctor_set(x_35, 1, x_83);
lean_ctor_set(x_35, 0, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_35);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_74, 0, x_84);
return x_74;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_74, 1);
lean_inc(x_85);
lean_dec(x_74);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
lean_ctor_set(x_35, 1, x_89);
lean_ctor_set(x_35, 0, x_86);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_35);
lean_ctor_set(x_90, 1, x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_free_object(x_35);
x_92 = !lean_is_exclusive(x_74);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_74, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
return x_74;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_75, 0);
x_96 = lean_ctor_get(x_75, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_75);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_74, 0, x_97);
return x_74;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_74, 1);
lean_inc(x_98);
lean_dec(x_74);
x_99 = lean_ctor_get(x_75, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_75, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_101 = x_75;
} else {
 lean_dec_ref(x_75);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_free_object(x_35);
x_104 = !lean_is_exclusive(x_74);
if (x_104 == 0)
{
return x_74;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_74, 0);
x_106 = lean_ctor_get(x_74, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_74);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; uint8_t x_109; 
lean_free_object(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_2);
x_108 = lean_ctor_get(x_39, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_31);
x_110 = lean_ctor_get(x_39, 1);
lean_inc(x_110);
lean_dec(x_39);
x_111 = lean_box(0);
x_112 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_111, x_3, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_113 = lean_ctor_get(x_39, 1);
lean_inc(x_113);
lean_dec(x_39);
x_114 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_115 = lean_string_append(x_114, x_1);
x_116 = l_Lake_loadPackageCore___closed__3;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_string_append(x_117, x_29);
x_119 = l_Lake_loadPackageCore___closed__4;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_string_append(x_120, x_31);
lean_dec(x_31);
x_122 = l_Lake_loadPackageCore___closed__5;
x_123 = lean_string_append(x_121, x_122);
x_124 = lean_string_append(x_123, x_29);
x_125 = lean_string_append(x_124, x_114);
x_126 = 1;
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
x_128 = lean_array_push(x_3, x_127);
x_129 = lean_box(0);
x_130 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_129, x_128, x_113);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_35, 0);
x_132 = lean_ctor_get(x_35, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_35);
x_133 = l_System_FilePath_pathExists(x_34, x_132);
x_134 = lean_unbox(x_131);
lean_dec(x_131);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
lean_dec(x_29);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_31);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
x_139 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_140 = lean_string_append(x_139, x_1);
x_141 = l_Lake_loadPackageCore___closed__1;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_string_append(x_142, x_33);
lean_dec(x_33);
x_144 = l_Lake_loadPackageCore___closed__2;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_34);
lean_dec(x_34);
x_147 = lean_string_append(x_146, x_139);
x_148 = 3;
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = lean_array_get_size(x_3);
x_151 = lean_array_push(x_3, x_149);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
if (lean_is_scalar(x_138)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_138;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_137);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_34);
lean_dec(x_33);
x_154 = lean_ctor_get(x_133, 1);
lean_inc(x_154);
lean_dec(x_133);
lean_ctor_set(x_2, 4, x_31);
x_155 = l_Lake_loadTomlConfig(x_2, x_3, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_161 = x_156;
} else {
 lean_dec_ref(x_156);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
if (lean_is_scalar(x_158)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_158;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_157);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_167 = x_155;
} else {
 lean_dec_ref(x_155);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_156, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_170 = x_156;
} else {
 lean_dec_ref(x_156);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_155, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_155, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_175 = x_155;
} else {
 lean_dec_ref(x_155);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
else
{
lean_object* x_177; uint8_t x_178; 
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_2);
x_177 = lean_ctor_get(x_133, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_31);
x_179 = lean_ctor_get(x_133, 1);
lean_inc(x_179);
lean_dec(x_133);
x_180 = lean_box(0);
x_181 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_180, x_3, x_179);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_182 = lean_ctor_get(x_133, 1);
lean_inc(x_182);
lean_dec(x_133);
x_183 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_184 = lean_string_append(x_183, x_1);
x_185 = l_Lake_loadPackageCore___closed__3;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_string_append(x_186, x_29);
x_188 = l_Lake_loadPackageCore___closed__4;
x_189 = lean_string_append(x_187, x_188);
x_190 = lean_string_append(x_189, x_31);
lean_dec(x_31);
x_191 = l_Lake_loadPackageCore___closed__5;
x_192 = lean_string_append(x_190, x_191);
x_193 = lean_string_append(x_192, x_29);
x_194 = lean_string_append(x_193, x_183);
x_195 = 1;
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_195);
x_197 = lean_array_push(x_3, x_196);
x_198 = lean_box(0);
x_199 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_198, x_197, x_182);
return x_199;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_2);
x_200 = l_Lake_configFileExists___closed__1;
lean_inc(x_9);
x_201 = l_System_FilePath_addExtension(x_9, x_200);
x_202 = l_Lake_configFileExists___closed__2;
x_203 = l_System_FilePath_addExtension(x_9, x_202);
lean_inc(x_7);
x_204 = l_System_FilePath_join(x_7, x_8);
lean_inc(x_204);
x_205 = l_System_FilePath_join(x_204, x_201);
x_206 = l_System_FilePath_join(x_204, x_203);
x_207 = l_System_FilePath_pathExists(x_205, x_4);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = l_System_FilePath_pathExists(x_206, x_209);
x_212 = lean_unbox(x_208);
lean_dec(x_208);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; 
lean_dec(x_201);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_203);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
x_217 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_218 = lean_string_append(x_217, x_1);
x_219 = l_Lake_loadPackageCore___closed__1;
x_220 = lean_string_append(x_218, x_219);
x_221 = lean_string_append(x_220, x_205);
lean_dec(x_205);
x_222 = l_Lake_loadPackageCore___closed__2;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_string_append(x_223, x_206);
lean_dec(x_206);
x_225 = lean_string_append(x_224, x_217);
x_226 = 3;
x_227 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_226);
x_228 = lean_array_get_size(x_3);
x_229 = lean_array_push(x_3, x_227);
if (lean_is_scalar(x_210)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_210;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
if (lean_is_scalar(x_216)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_216;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_215);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_206);
lean_dec(x_205);
x_232 = lean_ctor_get(x_211, 1);
lean_inc(x_232);
lean_dec(x_211);
x_233 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_233, 0, x_5);
lean_ctor_set(x_233, 1, x_6);
lean_ctor_set(x_233, 2, x_7);
lean_ctor_set(x_233, 3, x_8);
lean_ctor_set(x_233, 4, x_203);
lean_ctor_set(x_233, 5, x_10);
lean_ctor_set(x_233, 6, x_11);
lean_ctor_set(x_233, 7, x_15);
lean_ctor_set(x_233, 8, x_16);
lean_ctor_set_uint8(x_233, sizeof(void*)*9, x_12);
lean_ctor_set_uint8(x_233, sizeof(void*)*9 + 1, x_13);
lean_ctor_set_uint8(x_233, sizeof(void*)*9 + 2, x_14);
x_234 = l_Lake_loadTomlConfig(x_233, x_3, x_232);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
x_241 = lean_box(0);
if (lean_is_scalar(x_210)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_210;
}
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_241);
if (lean_is_scalar(x_240)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_240;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_239);
if (lean_is_scalar(x_237)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_237;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_236);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_210);
x_245 = lean_ctor_get(x_234, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_246 = x_234;
} else {
 lean_dec_ref(x_234);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_235, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_235, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_249 = x_235;
} else {
 lean_dec_ref(x_235);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_245);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_210);
x_252 = lean_ctor_get(x_234, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_234, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_254 = x_234;
} else {
 lean_dec_ref(x_234);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
else
{
lean_object* x_256; uint8_t x_257; 
lean_dec(x_210);
lean_dec(x_206);
lean_dec(x_205);
x_256 = lean_ctor_get(x_211, 0);
lean_inc(x_256);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_203);
x_258 = lean_ctor_get(x_211, 1);
lean_inc(x_258);
lean_dec(x_211);
x_259 = lean_box(0);
x_260 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_201, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_259, x_3, x_258);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_261 = lean_ctor_get(x_211, 1);
lean_inc(x_261);
lean_dec(x_211);
x_262 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_263 = lean_string_append(x_262, x_1);
x_264 = l_Lake_loadPackageCore___closed__3;
x_265 = lean_string_append(x_263, x_264);
x_266 = lean_string_append(x_265, x_201);
x_267 = l_Lake_loadPackageCore___closed__4;
x_268 = lean_string_append(x_266, x_267);
x_269 = lean_string_append(x_268, x_203);
lean_dec(x_203);
x_270 = l_Lake_loadPackageCore___closed__5;
x_271 = lean_string_append(x_269, x_270);
x_272 = lean_string_append(x_271, x_201);
x_273 = lean_string_append(x_272, x_262);
x_274 = 1;
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_274);
x_276 = lean_array_push(x_3, x_275);
x_277 = lean_box(0);
x_278 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_8, x_201, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_277, x_276, x_261);
return x_278;
}
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_279 = lean_ctor_get(x_17, 0);
lean_inc(x_279);
lean_dec(x_17);
x_280 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_281 = l_System_FilePath_join(x_280, x_9);
lean_dec(x_9);
x_282 = l_System_FilePath_pathExists(x_281, x_4);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_unbox(x_283);
lean_dec(x_283);
if (x_284 == 0)
{
uint8_t x_285; 
lean_dec(x_279);
lean_dec(x_2);
x_285 = !lean_is_exclusive(x_282);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_286 = lean_ctor_get(x_282, 0);
lean_dec(x_286);
x_287 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_288 = lean_string_append(x_287, x_1);
x_289 = l_Lake_loadPackageCore___closed__6;
x_290 = lean_string_append(x_288, x_289);
x_291 = lean_string_append(x_290, x_281);
lean_dec(x_281);
x_292 = lean_string_append(x_291, x_287);
x_293 = 3;
x_294 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set_uint8(x_294, sizeof(void*)*1, x_293);
x_295 = lean_array_get_size(x_3);
x_296 = lean_array_push(x_3, x_294);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set(x_282, 0, x_297);
return x_282;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_298 = lean_ctor_get(x_282, 1);
lean_inc(x_298);
lean_dec(x_282);
x_299 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_300 = lean_string_append(x_299, x_1);
x_301 = l_Lake_loadPackageCore___closed__6;
x_302 = lean_string_append(x_300, x_301);
x_303 = lean_string_append(x_302, x_281);
lean_dec(x_281);
x_304 = lean_string_append(x_303, x_299);
x_305 = 3;
x_306 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set_uint8(x_306, sizeof(void*)*1, x_305);
x_307 = lean_array_get_size(x_3);
x_308 = lean_array_push(x_3, x_306);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_298);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_282, 1);
lean_inc(x_311);
lean_dec(x_282);
x_312 = lean_box(0);
x_313 = l_Lake_loadPackageCore___lambda__3(x_279, x_1, x_281, x_2, x_312, x_3, x_311);
lean_dec(x_281);
lean_dec(x_279);
return x_313;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = lean_unbox(x_10);
lean_dec(x_10);
x_19 = l_Lake_loadPackageCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_18, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_13);
return x_19;
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
