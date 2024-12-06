// Lean compiler output
// Module: Std.Time.Zoned.Database.Windows
// Imports: Init.Data.SInt.Basic Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Time.Zoned.ZoneRules Std.Time.Zoned.Database.Basic
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst;
lean_object* lean_int64_to_int_sint(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3;
static lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1;
static lean_object* l_Std_Time_Database_WindowsDb_inst___closed__2;
static lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__2;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__4;
uint64_t lean_int64_neg(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___lambda__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_WindowsDb_inst___closed__3;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_windows_get_next_transition(lean_object*, uint64_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_WindowsDb_inst___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__5;
uint64_t lean_int64_of_nat(lean_object*);
static uint64_t l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx___boxed(lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Bind_bindLeft___at_Std_Time_Database_WindowsDb_inst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1___boxed__const__1;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_default;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_windows_get_next_transition(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_get_windows_local_timezone_id_at(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = 0;
x_7 = 1;
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
static uint64_t _init_l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_cstr_to_nat("32503690800");
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = 0;
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_windows_get_next_transition(x_1, x_8, x_7, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_unbox_uint64(x_5);
x_20 = lean_int64_to_int_sint(x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_6, x_24);
x_26 = lean_unbox_uint64(x_21);
x_27 = lean_unbox_uint64(x_5);
x_28 = lean_int64_dec_le(x_26, x_27);
if (x_28 == 0)
{
uint64_t x_29; uint64_t x_30; uint8_t x_31; 
x_29 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1;
x_30 = lean_unbox_uint64(x_21);
lean_dec(x_21);
x_31 = lean_int64_dec_le(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_9);
lean_free_object(x_2);
x_32 = lean_box(0);
x_33 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_34 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1(x_18, x_25, x_33, x_32, x_16);
lean_dec(x_18);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_2 = x_37;
x_3 = x_36;
goto _start;
}
else
{
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_dec(x_21);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
lean_dec(x_10);
x_41 = lean_unbox_uint64(x_5);
x_42 = lean_int64_to_int_sint(x_41);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
x_45 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_push(x_6, x_46);
x_48 = lean_unbox_uint64(x_43);
x_49 = lean_unbox_uint64(x_5);
x_50 = lean_int64_dec_le(x_48, x_49);
if (x_50 == 0)
{
uint64_t x_51; uint64_t x_52; uint8_t x_53; 
x_51 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1;
x_52 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_53 = lean_int64_dec_le(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_2);
x_54 = lean_box(0);
x_55 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_56 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1(x_40, x_47, x_55, x_54, x_39);
lean_dec(x_40);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_2 = x_59;
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_61; 
lean_dec(x_40);
lean_ctor_set(x_2, 1, x_47);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_39);
return x_61;
}
}
else
{
lean_object* x_62; 
lean_dec(x_43);
lean_dec(x_40);
lean_ctor_set(x_2, 1, x_47);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_39);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
return x_9;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint64_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_2);
x_69 = 0;
x_70 = lean_unbox_uint64(x_67);
x_71 = lean_windows_get_next_transition(x_1, x_70, x_69, x_3);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint64_t x_87; uint64_t x_88; uint8_t x_89; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_unbox_uint64(x_67);
x_81 = lean_int64_to_int_sint(x_80);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
x_84 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_push(x_68, x_85);
x_87 = lean_unbox_uint64(x_82);
x_88 = lean_unbox_uint64(x_67);
x_89 = lean_int64_dec_le(x_87, x_88);
if (x_89 == 0)
{
uint64_t x_90; uint64_t x_91; uint8_t x_92; 
x_90 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1;
x_91 = lean_unbox_uint64(x_82);
lean_dec(x_82);
x_92 = lean_int64_dec_le(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; uint64_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_78);
x_93 = lean_box(0);
x_94 = lean_unbox_uint64(x_67);
lean_dec(x_67);
x_95 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1(x_79, x_86, x_94, x_93, x_77);
lean_dec(x_79);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_2 = x_98;
x_3 = x_97;
goto _start;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_79);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_67);
lean_ctor_set(x_100, 1, x_86);
if (lean_is_scalar(x_78)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_78;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_77);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_82);
lean_dec(x_79);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_67);
lean_ctor_set(x_102, 1, x_86);
if (lean_is_scalar(x_78)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_78;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_77);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_68);
lean_dec(x_67);
x_104 = lean_ctor_get(x_71, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_71, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_106 = x_71;
} else {
 lean_dec_ref(x_71);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___lambda__1(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box_uint64(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1(x_1, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_4);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_2 = lean_int64_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find first transition in zone rules", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__4;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Std_Time_Database_Windows_getZoneRules___closed__2;
x_4 = 1;
x_5 = lean_windows_get_next_transition(x_1, x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Std_Time_Database_Windows_getZoneRules___closed__5;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Std_Time_Database_Windows_getZoneRules___closed__5;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_Database_Windows_getZoneRules___closed__3;
x_18 = l_Std_Time_Database_Windows_getZoneRules___lambda__1(x_1, x_3, x_17, x_16, x_13);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Time_Database_Windows_getZoneRules___lambda__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_Windows_getZoneRules(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_WindowsDb_toCtorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_noConfusion___rarg___boxed), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_WindowsDb_noConfusion___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Time_Database_WindowsDb_noConfusion(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft___at_Std_Time_Database_WindowsDb_inst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_Windows_getZoneRules(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__2;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_Windows_getZoneRules___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__2;
x_4 = l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1;
x_5 = l_Bind_bindLeft___at_Std_Time_Database_WindowsDb_inst___spec__1(x_3, x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_inst___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_inst___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_WindowsDb_inst___closed__1;
x_2 = l_Std_Time_Database_WindowsDb_inst___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Time_Database_WindowsDb_inst___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_WindowsDb_inst___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_WindowsDb_inst___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Std_Time_Database_Windows_getZoneRules___spec__1___closed__1();
l_Std_Time_Database_Windows_getZoneRules___closed__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__1();
l_Std_Time_Database_Windows_getZoneRules___closed__2 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__2();
l_Std_Time_Database_Windows_getZoneRules___closed__3 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__3();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3);
l_Std_Time_Database_Windows_getZoneRules___closed__4 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__4();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__4);
l_Std_Time_Database_Windows_getZoneRules___closed__5 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__5();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__5);
l_Std_Time_Database_WindowsDb_default = _init_l_Std_Time_Database_WindowsDb_default();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_default);
l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1___boxed__const__1 = _init_l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1___boxed__const__1();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1___boxed__const__1);
l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1 = _init_l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__1);
l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__2 = _init_l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__2();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___lambda__2___closed__2);
l_Std_Time_Database_WindowsDb_inst___closed__1 = _init_l_Std_Time_Database_WindowsDb_inst___closed__1();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___closed__1);
l_Std_Time_Database_WindowsDb_inst___closed__2 = _init_l_Std_Time_Database_WindowsDb_inst___closed__2();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___closed__2);
l_Std_Time_Database_WindowsDb_inst___closed__3 = _init_l_Std_Time_Database_WindowsDb_inst___closed__3();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___closed__3);
l_Std_Time_Database_WindowsDb_inst = _init_l_Std_Time_Database_WindowsDb_inst();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
