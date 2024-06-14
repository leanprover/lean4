// Lean compiler output
// Module: Leanpkg.Proc
// Imports: Init
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
lean_object* l_List_map___at_Leanpkg_execCmd___spec__1(lean_object*);
lean_object* l_List_foldl___at_String_join___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Leanpkg_execCmd(lean_object*, lean_object*);
lean_object* l_Leanpkg_execCmd_match__1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Leanpkg_execCmd_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_execCmd___closed__2;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Leanpkg_execCmd___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__3;
lean_object* l_Leanpkg_execCmd___closed__3;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Leanpkg_execCmd_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_execCmd_match__2(lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
extern lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
lean_object* l_Leanpkg_execCmd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Leanpkg_execCmd_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_execCmd_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Leanpkg_execCmd_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Leanpkg_execCmd_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_execCmd_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_map___at_Leanpkg_execCmd___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___at_Leanpkg_execCmd___spec__1(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
x_11 = l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__3;
x_12 = lean_string_append(x_10, x_11);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_append(x_12, x_9);
x_14 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_15 = lean_string_append(x_13, x_14);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = l_List_map___at_Leanpkg_execCmd___spec__1(x_21);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_instInhabitedParserDescr___closed__1;
x_26 = lean_string_append(x_25, x_23);
lean_dec(x_23);
x_27 = l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__3;
x_28 = lean_string_append(x_26, x_27);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_string_append(x_28, x_25);
x_30 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_string_append(x_28, x_33);
lean_dec(x_33);
x_35 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_22);
return x_37;
}
}
}
}
}
static lean_object* _init_l_Leanpkg_execCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("> ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("external command exited with status ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("    # in directory ");
return x_1;
}
}
lean_object* l_Leanpkg_execCmd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_66; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_array_to_list(lean_box(0), x_3);
x_5 = l_List_map___at_Leanpkg_execCmd___spec__1(x_4);
x_6 = l_Lean_instInhabitedParserDescr___closed__1;
x_7 = l_List_foldl___at_String_join___spec__1(x_6, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_array_to_list(lean_box(0), x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_13 = l_String_intercalate(x_12, x_11);
x_14 = l_Leanpkg_execCmd___closed__1;
x_15 = lean_string_append(x_14, x_7);
lean_dec(x_7);
x_66 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
x_16 = x_13;
goto block_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Leanpkg_execCmd___closed__3;
x_69 = lean_string_append(x_13, x_68);
x_70 = lean_string_append(x_69, x_67);
lean_dec(x_67);
x_16 = x_70;
goto block_65;
}
block_65:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_IO_println___at_Lean_instEval___spec__1(x_17, x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_1);
x_20 = lean_io_process_spawn(x_1, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_io_process_child_wait(x_23, x_21, x_22);
lean_dec(x_21);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = 0;
x_28 = lean_unbox_uint32(x_26);
x_29 = x_28 == x_27;
if (x_29 == 0)
{
uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_unbox_uint32(x_26);
lean_dec(x_26);
x_31 = lean_uint32_to_nat(x_30);
x_32 = l_Nat_repr(x_31);
x_33 = l_Leanpkg_execCmd___closed__2;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = lean_string_append(x_34, x_6);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
else
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_box(0);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint32_t x_40; uint32_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = 0;
x_41 = lean_unbox_uint32(x_38);
x_42 = x_41 == x_40;
if (x_42 == 0)
{
uint32_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_unbox_uint32(x_38);
lean_dec(x_38);
x_44 = lean_uint32_to_nat(x_43);
x_45 = l_Nat_repr(x_44);
x_46 = l_Leanpkg_execCmd___closed__2;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = lean_string_append(x_47, x_6);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_39);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_24);
if (x_53 == 0)
{
return x_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_24, 0);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_24);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Leanpkg_Proc(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Leanpkg_execCmd___closed__1 = _init_l_Leanpkg_execCmd___closed__1();
lean_mark_persistent(l_Leanpkg_execCmd___closed__1);
l_Leanpkg_execCmd___closed__2 = _init_l_Leanpkg_execCmd___closed__2();
lean_mark_persistent(l_Leanpkg_execCmd___closed__2);
l_Leanpkg_execCmd___closed__3 = _init_l_Leanpkg_execCmd___closed__3();
lean_mark_persistent(l_Leanpkg_execCmd___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
