// Lean compiler output
// Module: Std.Time.Zoned.Database.Windows
// Imports: public import Init.Data.SInt.Basic public import Std.Time.Zoned.Database.Basic import Init.While
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
lean_object* lean_windows_get_next_transition(lean_object*, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0;
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__0;
uint64_t lean_int64_neg(uint64_t);
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Time_Database_Windows_getZoneRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__2 = (const lean_object*)&l_Std_Time_Database_Windows_getZoneRules___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3;
static const lean_string_object l_Std_Time_Database_Windows_getZoneRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "cannot find first transition in zone rules"};
static const lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__4 = (const lean_object*)&l_Std_Time_Database_Windows_getZoneRules___closed__4_value;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_default;
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Database_WindowsDb_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_WindowsDb_inst___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_WindowsDb_inst___closed__0 = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__0_value;
static const lean_closure_object l_Std_Time_Database_WindowsDb_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_WindowsDb_inst___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_WindowsDb_inst___closed__1 = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__1_value;
static const lean_ctor_object l_Std_Time_Database_WindowsDb_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__0_value),((lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__1_value)}};
static const lean_object* l_Std_Time_Database_WindowsDb_inst___closed__2 = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_WindowsDb_inst = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_6 = lean_unbox(x_3);
x_7 = lean_windows_get_next_transition(x_1, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_get_windows_local_timezone_id_at(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = 0;
x_7 = 1;
lean_inc_ref(x_3);
lean_inc_ref(x_4);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint64_t _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_cstr_to_nat("32503690800");
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_60; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_60 = !lean_is_exclusive(x_2);
if (x_60 == 0)
{
x_6 = x_2;
x_7 = x_60;
goto block_59;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_60;
goto block_59;
}
block_59:
{
uint8_t x_8; uint64_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_unbox_uint64(x_4);
x_10 = lean_windows_get_next_transition(x_1, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_50; 
x_11 = lean_ctor_get(x_10, 0);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
x_12 = x_10;
x_13 = x_50;
goto block_49;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_42; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
x_17 = x_14;
x_18 = x_42;
goto block_41;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = x_42;
goto block_41;
}
block_41:
{
uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_31; uint64_t x_32; uint8_t x_33; 
x_19 = lean_unbox_uint64(x_4);
x_20 = lean_int64_to_int_sint(x_19);
x_21 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_16);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_push(x_5, x_22);
x_31 = lean_unbox_uint64(x_15);
x_32 = lean_unbox_uint64(x_4);
x_33 = lean_int64_dec_le(x_31, x_32);
if (x_33 == 0)
{
uint64_t x_34; uint64_t x_35; uint8_t x_36; 
x_34 = lean_uint64_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0);
x_35 = lean_unbox_uint64(x_15);
x_36 = lean_int64_dec_le(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_del_object(x_17);
lean_del_object(x_12);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_23);
lean_ctor_set(x_6, 0, x_15);
x_37 = x_6;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_23);
x_37 = x_40;
goto block_39;
}
block_39:
{
x_2 = x_37;
goto _start;
}
}
else
{
lean_dec(x_15);
lean_del_object(x_6);
goto block_30;
}
}
else
{
lean_dec(x_15);
lean_del_object(x_6);
goto block_30;
}
block_30:
{
lean_object* x_24; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_23);
lean_ctor_set(x_17, 0, x_4);
x_24 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_23);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_24);
x_25 = x_12;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_11);
if (x_7 == 0)
{
x_43 = x_6;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_43);
x_44 = x_12;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_del_object(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = lean_ctor_get(x_10, 0);
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
x_52 = x_10;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_10);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__1(void) {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__0, &l_Std_Time_Database_Windows_getZoneRules___closed__0_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__0);
x_2 = lean_int64_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1(void) {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__2));
x_2 = l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__4));
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* x_1) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
x_4 = 1;
x_5 = lean_windows_get_next_transition(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_44; 
x_6 = lean_ctor_get(x_5, 0);
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
x_7 = x_5;
x_8 = x_44;
goto block_43;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_44;
goto block_43;
}
block_43:
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_del_object(x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__3, &l_Std_Time_Database_Windows_getZoneRules___closed__3_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__3);
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_30; 
x_12 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_13 = x_11;
x_14 = x_30;
goto block_29;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_27; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_12, 1);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_12, 0);
lean_dec(x_28);
x_17 = x_12;
x_18 = x_27;
goto block_26;
}
else
{
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_16);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_20);
x_21 = x_13;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_9);
x_31 = lean_ctor_get(x_11, 0);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
x_32 = x_11;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
x_39 = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__5, &l_Std_Time_Database_Windows_getZoneRules___closed__5_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__5);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_39);
x_40 = x_7;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
x_45 = lean_ctor_get(x_5, 0);
x_52 = !lean_is_exclusive(x_5);
if (x_52 == 0)
{
x_46 = x_5;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_Windows_getZoneRules(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
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
static lean_object* _init_l_Std_Time_Database_WindowsDb_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_Windows_getZoneRules(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_WindowsDb_inst___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object* x_1) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
x_4 = lean_get_windows_local_timezone_id_at(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_Database_Windows_getZoneRules(x_5);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_7 = lean_ctor_get(x_4, 0);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
x_8 = x_4;
x_9 = x_14;
goto block_13;
}
else
{
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_WindowsDb_inst___lam__1(x_1);
return x_3;
}
}
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_SInt_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1);
l_Std_Time_Database_WindowsDb_default = _init_l_Std_Time_Database_WindowsDb_default();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_default);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_Windows(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_Windows(builtin);
}
#ifdef __cplusplus
}
#endif
