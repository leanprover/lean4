// Lean compiler output
// Module: Std.Time.Zoned.Database.TZdb
// Imports: Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Time.Zoned.ZoneRules Std.Time.Zoned.Database.Basic
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
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__2;
lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object*);
static lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__2;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZif(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_inst___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_inst___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2;
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1;
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__3;
lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__5;
static lean_object* l_Std_Time_Database_TZdb_parseTZif___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_default;
static lean_object* l_Std_Time_Database_TZdb_default___closed__1;
static lean_object* l_Std_Time_Database_TZdb_localRules___lambda__1___closed__1;
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__1;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Std_Time_Database_TZdb_parseTZIfFromDisk___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lambda__2(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_inst___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Std_Time_Database_TZdb_localRules___lambda__1___closed__2;
static lean_object* l_Std_Time_Database_TZdb_default___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_default___closed__3;
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__3;
lean_object* l_IO_Process_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__1;
lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_Database_TZdb_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/etc/localtime", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/usr/share/zoneinfo/", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_TZdb_default___closed__1;
x_2 = l_Std_Time_Database_TZdb_default___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Time_Database_TZdb_default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_parseTZif___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_TimeZone_TZif_parse), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZif(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Time_Database_TZdb_parseTZif___closed__1;
x_4 = l_Std_Internal_Parsec_ByteArray_Parser_run___rarg(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Std_Time_TimeZone_convertTZif(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Std_Time_Database_TZdb_parseTZIfFromDisk___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 18);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_Time_Database_TZdb_parseTZif(x_2, x_1);
x_5 = l_IO_ofExcept___at_Std_Time_Database_TZdb_parseTZIfFromDisk___spec__1(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in the local timezone database", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readBinFile(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Std_Time_Database_TZdb_parseTZIfFromDisk___lambda__1(x_2, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1;
x_11 = lean_string_append(x_10, x_2);
lean_dec(x_2);
x_12 = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1;
x_17 = lean_string_append(x_16, x_2);
lean_dec(x_2);
x_18 = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_TZdb_parseTZIfFromDisk(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_idFromPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zoneinfo", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_idFromPath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_TZdb_idFromPath___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_idFromPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_System_FilePath_components(x_1);
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
x_7 = l_Array_get_x3f___rarg(x_3, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = l_Array_get_x3f___rarg(x_3, x_12);
lean_dec(x_12);
lean_dec(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
lean_dec(x_10);
x_14 = lean_box(0);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = l_Std_Time_Database_TZdb_idFromPath___closed__2;
x_18 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1(x_13, x_17);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Time_Database_TZdb_idFromPath___closed__3;
x_20 = lean_string_append(x_16, x_19);
x_21 = lean_string_append(x_20, x_10);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_dec(x_16);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Std_Time_Database_TZdb_idFromPath___closed__2;
x_25 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Std_Time_Database_TZdb_idFromPath___closed__3;
x_27 = lean_string_append(x_22, x_26);
x_28 = lean_string_append(x_27, x_10);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_28);
return x_7;
}
else
{
lean_dec(x_22);
return x_7;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_4, x_30);
lean_dec(x_4);
x_32 = l_Array_get_x3f___rarg(x_3, x_31);
lean_dec(x_31);
lean_dec(x_3);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_29);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
lean_inc(x_34);
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
x_37 = l_Std_Time_Database_TZdb_idFromPath___closed__2;
x_38 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Std_Time_Database_TZdb_idFromPath___closed__3;
x_40 = lean_string_append(x_34, x_39);
x_41 = lean_string_append(x_40, x_29);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_29);
return x_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Std_Time_Database_TZdb_idFromPath___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot read the id of the path.", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_TZdb_localRules___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_TZdb_idFromPath(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Time_Database_TZdb_localRules___lambda__1___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Std_Time_Database_TZdb_parseTZIfFromDisk(x_1, x_7, x_3);
return x_8;
}
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("readlink", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find the local timezone database", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_TZdb_localRules___closed__5;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_box(0);
lean_inc(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Std_Time_Database_TZdb_localRules___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_mk(x_6);
x_8 = lean_box(0);
x_9 = l_Std_Time_Database_TZdb_localRules___closed__1;
x_10 = l_Std_Time_Database_TZdb_localRules___closed__4;
x_11 = l_Std_Time_Database_TZdb_localRules___closed__3;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_12);
x_14 = l_IO_Process_run(x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_Time_Database_TZdb_localRules___lambda__1(x_1, x_15, x_16);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = l_Std_Time_Database_TZdb_localRules___closed__6;
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Std_Time_Database_TZdb_localRules___closed__6;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_TZdb_localRules___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_System_FilePath_join(x_1, x_2);
x_5 = l_Std_Time_Database_TZdb_parseTZIfFromDisk(x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_Time_Database_TZdb_localRules(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_TZdb_inst___lambda__1), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_TZdb_inst___lambda__2), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_TZdb_inst___closed__1;
x_2 = l_Std_Time_Database_TZdb_inst___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Time_Database_TZdb_inst___closed__3;
return x_1;
}
}
lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_TimeZone(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Database_TZdb_default___closed__1 = _init_l_Std_Time_Database_TZdb_default___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_default___closed__1);
l_Std_Time_Database_TZdb_default___closed__2 = _init_l_Std_Time_Database_TZdb_default___closed__2();
lean_mark_persistent(l_Std_Time_Database_TZdb_default___closed__2);
l_Std_Time_Database_TZdb_default___closed__3 = _init_l_Std_Time_Database_TZdb_default___closed__3();
lean_mark_persistent(l_Std_Time_Database_TZdb_default___closed__3);
l_Std_Time_Database_TZdb_default = _init_l_Std_Time_Database_TZdb_default();
lean_mark_persistent(l_Std_Time_Database_TZdb_default);
l_Std_Time_Database_TZdb_parseTZif___closed__1 = _init_l_Std_Time_Database_TZdb_parseTZif___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_parseTZif___closed__1);
l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1 = _init_l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1);
l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2 = _init_l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2();
lean_mark_persistent(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2);
l_Std_Time_Database_TZdb_idFromPath___closed__1 = _init_l_Std_Time_Database_TZdb_idFromPath___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_idFromPath___closed__1);
l_Std_Time_Database_TZdb_idFromPath___closed__2 = _init_l_Std_Time_Database_TZdb_idFromPath___closed__2();
lean_mark_persistent(l_Std_Time_Database_TZdb_idFromPath___closed__2);
l_Std_Time_Database_TZdb_idFromPath___closed__3 = _init_l_Std_Time_Database_TZdb_idFromPath___closed__3();
lean_mark_persistent(l_Std_Time_Database_TZdb_idFromPath___closed__3);
l_Std_Time_Database_TZdb_localRules___lambda__1___closed__1 = _init_l_Std_Time_Database_TZdb_localRules___lambda__1___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___lambda__1___closed__1);
l_Std_Time_Database_TZdb_localRules___lambda__1___closed__2 = _init_l_Std_Time_Database_TZdb_localRules___lambda__1___closed__2();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___lambda__1___closed__2);
l_Std_Time_Database_TZdb_localRules___closed__1 = _init_l_Std_Time_Database_TZdb_localRules___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___closed__1);
l_Std_Time_Database_TZdb_localRules___closed__2 = _init_l_Std_Time_Database_TZdb_localRules___closed__2();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___closed__2);
l_Std_Time_Database_TZdb_localRules___closed__3 = _init_l_Std_Time_Database_TZdb_localRules___closed__3();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___closed__3);
l_Std_Time_Database_TZdb_localRules___closed__4 = _init_l_Std_Time_Database_TZdb_localRules___closed__4();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___closed__4);
l_Std_Time_Database_TZdb_localRules___closed__5 = _init_l_Std_Time_Database_TZdb_localRules___closed__5();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___closed__5);
l_Std_Time_Database_TZdb_localRules___closed__6 = _init_l_Std_Time_Database_TZdb_localRules___closed__6();
lean_mark_persistent(l_Std_Time_Database_TZdb_localRules___closed__6);
l_Std_Time_Database_TZdb_inst___closed__1 = _init_l_Std_Time_Database_TZdb_inst___closed__1();
lean_mark_persistent(l_Std_Time_Database_TZdb_inst___closed__1);
l_Std_Time_Database_TZdb_inst___closed__2 = _init_l_Std_Time_Database_TZdb_inst___closed__2();
lean_mark_persistent(l_Std_Time_Database_TZdb_inst___closed__2);
l_Std_Time_Database_TZdb_inst___closed__3 = _init_l_Std_Time_Database_TZdb_inst___closed__3();
lean_mark_persistent(l_Std_Time_Database_TZdb_inst___closed__3);
l_Std_Time_Database_TZdb_inst = _init_l_Std_Time_Database_TZdb_inst();
lean_mark_persistent(l_Std_Time_Database_TZdb_inst);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
