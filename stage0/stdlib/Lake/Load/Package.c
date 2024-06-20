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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__1(lean_object*);
static lean_object* l_Lake_configFileExists___closed__1;
extern lean_object* l_Lean_searchPathRef;
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__2;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
static lean_object* l_Lake_loadPackageCore___closed__5;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set(x_12, 4, x_5);
lean_ctor_set(x_12, 5, x_6);
lean_ctor_set(x_12, 6, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_7);
x_13 = l_Lake_loadLeanConfig(x_12, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_20 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_21 = l_Prod_map___rarg(x_19, x_20, x_18);
lean_ctor_set(x_14, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_25 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_26 = l_Prod_map___rarg(x_24, x_25, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
x_32 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_33 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_34 = l_Prod_map___rarg(x_32, x_33, x_29);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_13, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_13, 0, x_42);
return x_13;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_ctor_get(x_14, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
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
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lake_configFileExists___closed__1;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_13 = l_Lake_configFileExists___closed__2;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_16 = lean_string_append(x_15, x_2);
x_17 = l_Lake_loadPackageCore___lambda__3___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_3);
x_20 = lean_string_append(x_19, x_15);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_9);
x_24 = lean_array_push(x_9, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Lake_loadTomlConfig(x_4, x_5, x_6, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_27, 0, x_39);
return x_27;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_27, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_27;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_27, 0, x_53);
return x_27;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_dec(x_27);
x_55 = lean_ctor_get(x_28, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_57 = x_28;
} else {
 lean_dec_ref(x_28);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = l_Lake_loadLeanConfig(x_7, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_71 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_72 = l_Prod_map___rarg(x_70, x_71, x_69);
lean_ctor_set(x_65, 0, x_72);
return x_64;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_65, 0);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_65);
x_75 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_76 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_77 = l_Prod_map___rarg(x_75, x_76, x_73);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_64, 0, x_78);
return x_64;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_ctor_get(x_65, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_82 = x_65;
} else {
 lean_dec_ref(x_65);
 x_82 = lean_box(0);
}
x_83 = l_Lake_loadPackageCore___lambda__2___closed__1;
x_84 = l_Lake_loadPackageCore___lambda__2___closed__2;
x_85 = l_Prod_map___rarg(x_83, x_84, x_80);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_64);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_64, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
return x_64;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_65, 0);
x_92 = lean_ctor_get(x_65, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_65);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_64, 0, x_93);
return x_64;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_64, 1);
lean_inc(x_94);
lean_dec(x_64);
x_95 = lean_ctor_get(x_65, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_65, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_97 = x_65;
} else {
 lean_dec_ref(x_65);
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
x_100 = !lean_is_exclusive(x_64);
if (x_100 == 0)
{
return x_64;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_64, 0);
x_102 = lean_ctor_get(x_64, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_64);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
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
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_12 = lean_ctor_get(x_2, 6);
lean_inc(x_12);
lean_inc(x_8);
x_13 = l_System_FilePath_extension(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_2);
x_14 = l_Lake_configFileExists___closed__1;
lean_inc(x_8);
x_15 = l_System_FilePath_addExtension(x_8, x_14);
x_16 = l_Lake_configFileExists___closed__2;
x_17 = l_System_FilePath_addExtension(x_8, x_16);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_15);
lean_inc(x_18);
x_19 = l_System_FilePath_join(x_18, x_15);
lean_inc(x_17);
lean_inc(x_18);
x_20 = l_System_FilePath_join(x_18, x_17);
x_21 = l_System_FilePath_pathExists(x_19, x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_System_FilePath_pathExists(x_20, x_24);
x_26 = lean_unbox(x_23);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_32 = lean_string_append(x_31, x_1);
x_33 = l_Lake_loadPackageCore___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_19);
lean_dec(x_19);
x_36 = l_Lake_loadPackageCore___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_20);
lean_dec(x_20);
x_39 = lean_string_append(x_38, x_31);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_3);
x_43 = lean_array_push(x_3, x_41);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_43);
lean_ctor_set(x_21, 0, x_42);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
x_45 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_46 = lean_string_append(x_45, x_1);
x_47 = l_Lake_loadPackageCore___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_19);
lean_dec(x_19);
x_50 = l_Lake_loadPackageCore___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_20);
lean_dec(x_20);
x_53 = lean_string_append(x_52, x_45);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_3);
x_57 = lean_array_push(x_3, x_55);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_57);
lean_ctor_set(x_21, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_44);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_20);
lean_dec(x_19);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_dec(x_25);
x_60 = l_Lake_loadTomlConfig(x_18, x_7, x_17, x_3, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_box(0);
lean_ctor_set(x_21, 1, x_66);
lean_ctor_set(x_21, 0, x_65);
lean_ctor_set(x_61, 0, x_21);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_box(0);
lean_ctor_set(x_21, 1, x_69);
lean_ctor_set(x_21, 0, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_60, 0, x_70);
return x_60;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_ctor_get(x_61, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_74 = x_61;
} else {
 lean_dec_ref(x_61);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
lean_ctor_set(x_21, 1, x_75);
lean_ctor_set(x_21, 0, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_21);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_60, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_61);
if (x_80 == 0)
{
return x_60;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_61, 0);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_61);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_60, 0, x_83);
return x_60;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_60, 1);
lean_inc(x_84);
lean_dec(x_60);
x_85 = lean_ctor_get(x_61, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_87 = x_61;
} else {
 lean_dec_ref(x_61);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_free_object(x_21);
x_90 = !lean_is_exclusive(x_60);
if (x_90 == 0)
{
return x_60;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_60, 0);
x_92 = lean_ctor_get(x_60, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_60);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_free_object(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_94 = lean_ctor_get(x_25, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_17);
x_96 = lean_ctor_get(x_25, 1);
lean_inc(x_96);
lean_dec(x_25);
x_97 = lean_box(0);
x_98 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_97, x_3, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_99 = lean_ctor_get(x_25, 1);
lean_inc(x_99);
lean_dec(x_25);
x_100 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_101 = lean_string_append(x_100, x_1);
x_102 = l_Lake_loadPackageCore___closed__3;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_string_append(x_103, x_15);
x_105 = l_Lake_loadPackageCore___closed__4;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_string_append(x_106, x_17);
lean_dec(x_17);
x_108 = l_Lake_loadPackageCore___closed__5;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_string_append(x_109, x_15);
x_111 = lean_string_append(x_110, x_100);
x_112 = 1;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_array_push(x_3, x_113);
x_115 = lean_box(0);
x_116 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_115, x_114, x_99);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_21, 0);
x_118 = lean_ctor_get(x_21, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_21);
x_119 = l_System_FilePath_pathExists(x_20, x_118);
x_120 = lean_unbox(x_117);
lean_dec(x_117);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_126 = lean_string_append(x_125, x_1);
x_127 = l_Lake_loadPackageCore___closed__1;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_string_append(x_128, x_19);
lean_dec(x_19);
x_130 = l_Lake_loadPackageCore___closed__2;
x_131 = lean_string_append(x_129, x_130);
x_132 = lean_string_append(x_131, x_20);
lean_dec(x_20);
x_133 = lean_string_append(x_132, x_125);
x_134 = 3;
x_135 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_134);
x_136 = lean_array_get_size(x_3);
x_137 = lean_array_push(x_3, x_135);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
if (lean_is_scalar(x_124)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_124;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_123);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_20);
lean_dec(x_19);
x_140 = lean_ctor_get(x_119, 1);
lean_inc(x_140);
lean_dec(x_119);
x_141 = l_Lake_loadTomlConfig(x_18, x_7, x_17, x_3, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_146);
if (lean_is_scalar(x_144)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_144;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_143);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_141, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_153 = x_141;
} else {
 lean_dec_ref(x_141);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_142, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_156 = x_142;
} else {
 lean_dec_ref(x_142);
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
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_141, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_141, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_161 = x_141;
} else {
 lean_dec_ref(x_141);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; uint8_t x_164; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_163 = lean_ctor_get(x_119, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_17);
x_165 = lean_ctor_get(x_119, 1);
lean_inc(x_165);
lean_dec(x_119);
x_166 = lean_box(0);
x_167 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_166, x_3, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_168 = lean_ctor_get(x_119, 1);
lean_inc(x_168);
lean_dec(x_119);
x_169 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_170 = lean_string_append(x_169, x_1);
x_171 = l_Lake_loadPackageCore___closed__3;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_string_append(x_172, x_15);
x_174 = l_Lake_loadPackageCore___closed__4;
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_string_append(x_175, x_17);
lean_dec(x_17);
x_177 = l_Lake_loadPackageCore___closed__5;
x_178 = lean_string_append(x_176, x_177);
x_179 = lean_string_append(x_178, x_15);
x_180 = lean_string_append(x_179, x_169);
x_181 = 1;
x_182 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_181);
x_183 = lean_array_push(x_3, x_182);
x_184 = lean_box(0);
x_185 = l_Lake_loadPackageCore___lambda__2(x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_184, x_183, x_168);
return x_185;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_186 = lean_ctor_get(x_13, 0);
lean_inc(x_186);
lean_dec(x_13);
lean_inc(x_7);
x_187 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_8);
lean_inc(x_187);
x_188 = l_System_FilePath_join(x_187, x_8);
x_189 = l_System_FilePath_pathExists(x_188, x_4);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
uint8_t x_192; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_193 = lean_ctor_get(x_189, 0);
lean_dec(x_193);
x_194 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_195 = lean_string_append(x_194, x_1);
x_196 = l_Lake_loadPackageCore___closed__6;
x_197 = lean_string_append(x_195, x_196);
x_198 = lean_string_append(x_197, x_188);
lean_dec(x_188);
x_199 = lean_string_append(x_198, x_194);
x_200 = 3;
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_array_get_size(x_3);
x_203 = lean_array_push(x_3, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_189, 0, x_204);
return x_189;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_205 = lean_ctor_get(x_189, 1);
lean_inc(x_205);
lean_dec(x_189);
x_206 = l_Lake_loadPackageCore___lambda__3___closed__1;
x_207 = lean_string_append(x_206, x_1);
x_208 = l_Lake_loadPackageCore___closed__6;
x_209 = lean_string_append(x_207, x_208);
x_210 = lean_string_append(x_209, x_188);
lean_dec(x_188);
x_211 = lean_string_append(x_210, x_206);
x_212 = 3;
x_213 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*1, x_212);
x_214 = lean_array_get_size(x_3);
x_215 = lean_array_push(x_3, x_213);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_205);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_189, 1);
lean_inc(x_218);
lean_dec(x_189);
x_219 = lean_box(0);
x_220 = l_Lake_loadPackageCore___lambda__3(x_186, x_1, x_188, x_187, x_7, x_8, x_2, x_219, x_3, x_218);
lean_dec(x_188);
lean_dec(x_186);
return x_220;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_loadPackageCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_loadPackageCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
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
