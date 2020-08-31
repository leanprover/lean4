// Lean compiler output
// Module: Lean.Util.PPGoal
// Imports: Init Lean.Util.PPExt
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__2;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_ppGoal___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__5;
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__8;
lean_object* l_Lean_ppGoal___closed__7;
lean_object* l_Lean_ppGoal___closed__1;
lean_object* l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_System_FilePath_dirName___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 0;
lean_inc(x_2);
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_4, x_2);
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_13);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_6, x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(x_1, x_2, x_3, x_4, x_11, x_8);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_7, x_13);
lean_dec(x_7);
x_7 = x_14;
x_8 = x_12;
goto _start;
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :=");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_2);
x_24 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_11, 0, x_26);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_28);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_11, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_15, 1, x_32);
lean_ctor_set(x_15, 0, x_31);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_11);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_expr_eqv(x_38, x_35);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_List_isEmpty___rarg(x_18);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_20, 0, x_35);
if (x_40 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Format_isNil(x_21);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_46);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = l_List_reverse___rarg(x_18);
x_49 = l_Lean_Format_flatten___main___closed__1;
x_50 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_48, x_49);
x_51 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_44);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_44);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_44);
x_58 = lean_format_group(x_57);
x_59 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_44);
lean_ctor_set(x_24, 1, x_59);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = l_List_reverse___rarg(x_18);
x_63 = l_Lean_Format_flatten___main___closed__1;
x_64 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_62, x_63);
x_65 = 0;
x_66 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_65);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_69 = lean_box(1);
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_65);
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_65);
x_74 = lean_format_group(x_73);
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_21);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_65);
lean_ctor_set(x_24, 1, x_75);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_78; 
lean_dec(x_38);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_22);
lean_ctor_set(x_78, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_78);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_20, 0);
lean_inc(x_80);
lean_dec(x_20);
x_81 = lean_expr_eqv(x_80, x_35);
if (x_81 == 0)
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = l_List_isEmpty___rarg(x_18);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_22);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_35);
if (x_82 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Format_isNil(x_21);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_89, 0, x_21);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_87);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_80);
lean_ctor_set(x_24, 1, x_89);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = l_List_reverse___rarg(x_18);
x_92 = l_Lean_Format_flatten___main___closed__1;
x_93 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_91, x_92);
x_94 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_95 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_87);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_96 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_80);
x_97 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_87);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_87);
x_101 = lean_format_group(x_100);
x_102 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_87);
lean_ctor_set(x_24, 1, x_102);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_80);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_105 = l_List_reverse___rarg(x_18);
x_106 = l_Lean_Format_flatten___main___closed__1;
x_107 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_105, x_106);
x_108 = 0;
x_109 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_108);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_111 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_80);
x_112 = lean_box(1);
x_113 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_108);
x_117 = lean_format_group(x_116);
x_118 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_118, 0, x_21);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_108);
lean_ctor_set(x_24, 1, x_118);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_80);
lean_dec(x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_80);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_22);
lean_ctor_set(x_121, 1, x_18);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_122);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_121);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_24, 0);
lean_inc(x_124);
lean_dec(x_24);
x_125 = lean_ctor_get(x_20, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_126 = x_20;
} else {
 lean_dec_ref(x_20);
 x_126 = lean_box(0);
}
x_127 = lean_expr_eqv(x_125, x_124);
if (x_127 == 0)
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = l_List_isEmpty___rarg(x_18);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_22);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_124);
if (x_128 == 0)
{
uint8_t x_132; 
x_132 = l_Lean_Format_isNil(x_21);
if (x_132 == 0)
{
uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_133 = 0;
x_134 = lean_box(1);
x_135 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_135, 0, x_21);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_133);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_136; 
lean_dec(x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_15, 1, x_136);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_138 = l_List_reverse___rarg(x_18);
x_139 = l_Lean_Format_flatten___main___closed__1;
x_140 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_138, x_139);
x_141 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_142 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_133);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_143 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_125);
x_144 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_133);
x_145 = lean_unsigned_to_nat(2u);
x_146 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_133);
x_148 = lean_format_group(x_147);
x_149 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*2, x_133);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_15, 1, x_150);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_152; 
lean_dec(x_125);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_131);
lean_ctor_set(x_152, 1, x_21);
lean_ctor_set(x_15, 1, x_152);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_154 = l_List_reverse___rarg(x_18);
x_155 = l_Lean_Format_flatten___main___closed__1;
x_156 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_154, x_155);
x_157 = 0;
x_158 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_159 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*2, x_157);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_160 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_125);
x_161 = lean_box(1);
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_157);
x_163 = lean_unsigned_to_nat(2u);
x_164 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_157);
x_166 = lean_format_group(x_165);
x_167 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_167, 0, x_21);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*2, x_157);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_131);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_15, 1, x_168);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_170; 
lean_dec(x_125);
lean_dec(x_18);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_131);
lean_ctor_set(x_170, 1, x_21);
lean_ctor_set(x_15, 1, x_170);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_125);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_22);
lean_ctor_set(x_172, 1, x_18);
if (lean_is_scalar(x_126)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_126;
}
lean_ctor_set(x_173, 0, x_124);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_21);
lean_ctor_set(x_15, 1, x_174);
lean_ctor_set(x_15, 0, x_172);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_15, 0);
x_177 = lean_ctor_get(x_15, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_15);
x_178 = lean_ctor_get(x_17, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_17, 3);
lean_inc(x_179);
lean_dec(x_17);
lean_inc(x_2);
x_180 = l_Lean_MetavarContext_instantiateMVars(x_2, x_179);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_178);
lean_ctor_set(x_183, 1, x_18);
lean_ctor_set(x_11, 0, x_181);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_11);
lean_ctor_set(x_184, 1, x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_7 = x_13;
x_8 = x_185;
goto _start;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_free_object(x_11);
x_187 = lean_ctor_get(x_180, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_188 = x_180;
} else {
 lean_dec_ref(x_180);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_176, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_190 = x_176;
} else {
 lean_dec_ref(x_176);
 x_190 = lean_box(0);
}
x_191 = lean_expr_eqv(x_189, x_187);
if (x_191 == 0)
{
uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = l_List_isEmpty___rarg(x_18);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_178);
lean_ctor_set(x_194, 1, x_193);
if (lean_is_scalar(x_190)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_190;
}
lean_ctor_set(x_195, 0, x_187);
if (x_192 == 0)
{
uint8_t x_196; 
x_196 = l_Lean_Format_isNil(x_177);
if (x_196 == 0)
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; 
x_197 = 0;
x_198 = lean_box(1);
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_177);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_197);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_189);
if (lean_is_scalar(x_188)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_188;
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_200);
x_7 = x_13;
x_8 = x_201;
goto _start;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_203 = l_List_reverse___rarg(x_18);
x_204 = l_Lean_Format_flatten___main___closed__1;
x_205 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_203, x_204);
x_206 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_207 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*2, x_197);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_208 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_189);
x_209 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_209, 0, x_198);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_197);
x_210 = lean_unsigned_to_nat(2u);
x_211 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set_uint8(x_212, sizeof(void*)*2, x_197);
x_213 = lean_format_group(x_212);
x_214 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_214, 0, x_199);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_197);
if (lean_is_scalar(x_188)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_188;
}
lean_ctor_set(x_215, 0, x_195);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_194);
lean_ctor_set(x_216, 1, x_215);
x_7 = x_13;
x_8 = x_216;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_189);
if (lean_is_scalar(x_188)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_188;
}
lean_ctor_set(x_218, 0, x_195);
lean_ctor_set(x_218, 1, x_177);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_194);
lean_ctor_set(x_219, 1, x_218);
x_7 = x_13;
x_8 = x_219;
goto _start;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_221 = l_List_reverse___rarg(x_18);
x_222 = l_Lean_Format_flatten___main___closed__1;
x_223 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_221, x_222);
x_224 = 0;
x_225 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_226 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_224);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_227 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_189);
x_228 = lean_box(1);
x_229 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_224);
x_230 = lean_unsigned_to_nat(2u);
x_231 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_232, 0, x_226);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*2, x_224);
x_233 = lean_format_group(x_232);
x_234 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_234, 0, x_177);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*2, x_224);
if (lean_is_scalar(x_188)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_188;
}
lean_ctor_set(x_235, 0, x_195);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_194);
lean_ctor_set(x_236, 1, x_235);
x_7 = x_13;
x_8 = x_236;
goto _start;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_189);
lean_dec(x_18);
if (lean_is_scalar(x_188)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_188;
}
lean_ctor_set(x_238, 0, x_195);
lean_ctor_set(x_238, 1, x_177);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_194);
lean_ctor_set(x_239, 1, x_238);
x_7 = x_13;
x_8 = x_239;
goto _start;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_189);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_178);
lean_ctor_set(x_241, 1, x_18);
if (lean_is_scalar(x_190)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_190;
}
lean_ctor_set(x_242, 0, x_187);
if (lean_is_scalar(x_188)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_188;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_177);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
x_7 = x_13;
x_8 = x_244;
goto _start;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_free_object(x_11);
x_246 = lean_ctor_get(x_8, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_247 = x_8;
} else {
 lean_dec_ref(x_8);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_15, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_15, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_250 = x_15;
} else {
 lean_dec_ref(x_15);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_17, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_17, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_17, 4);
lean_inc(x_253);
lean_dec(x_17);
x_254 = l_List_isEmpty___rarg(x_246);
lean_inc(x_2);
x_255 = l_Lean_MetavarContext_instantiateMVars(x_2, x_252);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec(x_255);
lean_inc(x_2);
x_257 = l_Lean_MetavarContext_instantiateMVars(x_2, x_253);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_System_FilePath_dirName___closed__1;
x_260 = l_Lean_Name_toStringWithSep___main(x_259, x_251);
x_261 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = 0;
x_263 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_264 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set_uint8(x_264, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_265 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_256);
x_266 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set_uint8(x_266, sizeof(void*)*2, x_262);
x_267 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_268 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set_uint8(x_268, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_269 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_258);
x_270 = lean_box(1);
x_271 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*2, x_262);
x_272 = lean_unsigned_to_nat(2u);
x_273 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_268);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_262);
x_275 = lean_format_group(x_274);
x_276 = lean_box(0);
x_277 = lean_box(0);
if (x_254 == 0)
{
uint8_t x_290; 
x_290 = l_Lean_Format_isNil(x_249);
if (x_290 == 0)
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_291, 0, x_249);
lean_ctor_set(x_291, 1, x_270);
lean_ctor_set_uint8(x_291, sizeof(void*)*2, x_262);
if (lean_obj_tag(x_246) == 0)
{
lean_dec(x_248);
x_278 = x_291;
goto block_289;
}
else
{
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_246);
x_278 = x_291;
goto block_289;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_292 = lean_ctor_get(x_248, 0);
lean_inc(x_292);
lean_dec(x_248);
x_293 = l_List_reverse___rarg(x_246);
x_294 = l_Lean_Format_flatten___main___closed__1;
x_295 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_293, x_294);
x_296 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_297 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_298 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_292);
x_299 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_299, 0, x_270);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_262);
x_300 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_300, 0, x_272);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*2, x_262);
x_302 = lean_format_group(x_301);
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_291);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_262);
x_278 = x_303;
goto block_289;
}
}
}
else
{
if (lean_obj_tag(x_246) == 0)
{
lean_dec(x_248);
x_278 = x_249;
goto block_289;
}
else
{
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_246);
x_278 = x_249;
goto block_289;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_304 = lean_ctor_get(x_248, 0);
lean_inc(x_304);
lean_dec(x_248);
x_305 = l_List_reverse___rarg(x_246);
x_306 = l_Lean_Format_flatten___main___closed__1;
x_307 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_305, x_306);
x_308 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_309 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set_uint8(x_309, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_310 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_304);
x_311 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_311, 0, x_270);
lean_ctor_set(x_311, 1, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*2, x_262);
x_312 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_312, 0, x_272);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*2, x_262);
x_314 = lean_format_group(x_313);
x_315 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_315, 0, x_249);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_uint8(x_315, sizeof(void*)*2, x_262);
x_278 = x_315;
goto block_289;
}
}
}
}
else
{
lean_dec(x_248);
lean_dec(x_246);
x_278 = x_249;
goto block_289;
}
block_289:
{
uint8_t x_279; 
x_279 = l_Lean_Format_isNil(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_270);
lean_ctor_set_uint8(x_280, sizeof(void*)*2, x_262);
x_281 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_275);
lean_ctor_set_uint8(x_281, sizeof(void*)*2, x_262);
if (lean_is_scalar(x_250)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_250;
}
lean_ctor_set(x_282, 0, x_277);
lean_ctor_set(x_282, 1, x_281);
if (lean_is_scalar(x_247)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_247;
}
lean_ctor_set(x_283, 0, x_276);
lean_ctor_set(x_283, 1, x_282);
x_7 = x_13;
x_8 = x_283;
goto _start;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_285, 0, x_278);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set_uint8(x_285, sizeof(void*)*2, x_262);
if (lean_is_scalar(x_250)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_250;
}
lean_ctor_set(x_286, 0, x_277);
lean_ctor_set(x_286, 1, x_285);
if (lean_is_scalar(x_247)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_247;
}
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_286);
x_7 = x_13;
x_8 = x_287;
goto _start;
}
}
}
}
else
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_11, 0);
lean_inc(x_316);
lean_dec(x_11);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_8, 0);
lean_inc(x_317);
lean_dec(x_8);
x_318 = lean_ctor_get(x_15, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_15, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_320 = x_15;
} else {
 lean_dec_ref(x_15);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_316, 2);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 3);
lean_inc(x_322);
lean_dec(x_316);
lean_inc(x_2);
x_323 = l_Lean_MetavarContext_instantiateMVars(x_2, x_322);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_321);
lean_ctor_set(x_326, 1, x_317);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_324);
if (lean_is_scalar(x_325)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_325;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_320;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_328);
x_7 = x_13;
x_8 = x_329;
goto _start;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_323, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_332 = x_323;
} else {
 lean_dec_ref(x_323);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_318, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_334 = x_318;
} else {
 lean_dec_ref(x_318);
 x_334 = lean_box(0);
}
x_335 = lean_expr_eqv(x_333, x_331);
if (x_335 == 0)
{
uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = l_List_isEmpty___rarg(x_317);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_321);
lean_ctor_set(x_338, 1, x_337);
if (lean_is_scalar(x_334)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_334;
}
lean_ctor_set(x_339, 0, x_331);
if (x_336 == 0)
{
uint8_t x_340; 
x_340 = l_Lean_Format_isNil(x_319);
if (x_340 == 0)
{
uint8_t x_341; lean_object* x_342; lean_object* x_343; 
x_341 = 0;
x_342 = lean_box(1);
x_343 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_343, 0, x_319);
lean_ctor_set(x_343, 1, x_342);
lean_ctor_set_uint8(x_343, sizeof(void*)*2, x_341);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_332;
}
lean_ctor_set(x_344, 0, x_339);
lean_ctor_set(x_344, 1, x_343);
if (lean_is_scalar(x_320)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_320;
}
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_344);
x_7 = x_13;
x_8 = x_345;
goto _start;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_347 = l_List_reverse___rarg(x_317);
x_348 = l_Lean_Format_flatten___main___closed__1;
x_349 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_347, x_348);
x_350 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_351 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*2, x_341);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_352 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_353 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*2, x_341);
x_354 = lean_unsigned_to_nat(2u);
x_355 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
x_356 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set_uint8(x_356, sizeof(void*)*2, x_341);
x_357 = lean_format_group(x_356);
x_358 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_358, 0, x_343);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*2, x_341);
if (lean_is_scalar(x_332)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_332;
}
lean_ctor_set(x_359, 0, x_339);
lean_ctor_set(x_359, 1, x_358);
if (lean_is_scalar(x_320)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_320;
}
lean_ctor_set(x_360, 0, x_338);
lean_ctor_set(x_360, 1, x_359);
x_7 = x_13;
x_8 = x_360;
goto _start;
}
}
else
{
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_332;
}
lean_ctor_set(x_362, 0, x_339);
lean_ctor_set(x_362, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_320;
}
lean_ctor_set(x_363, 0, x_338);
lean_ctor_set(x_363, 1, x_362);
x_7 = x_13;
x_8 = x_363;
goto _start;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_365 = l_List_reverse___rarg(x_317);
x_366 = l_Lean_Format_flatten___main___closed__1;
x_367 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_365, x_366);
x_368 = 0;
x_369 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_370 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*2, x_368);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_371 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_372 = lean_box(1);
x_373 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*2, x_368);
x_374 = lean_unsigned_to_nat(2u);
x_375 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_376, 0, x_370);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set_uint8(x_376, sizeof(void*)*2, x_368);
x_377 = lean_format_group(x_376);
x_378 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_378, 0, x_319);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*2, x_368);
if (lean_is_scalar(x_332)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_332;
}
lean_ctor_set(x_379, 0, x_339);
lean_ctor_set(x_379, 1, x_378);
if (lean_is_scalar(x_320)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_320;
}
lean_ctor_set(x_380, 0, x_338);
lean_ctor_set(x_380, 1, x_379);
x_7 = x_13;
x_8 = x_380;
goto _start;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_333);
lean_dec(x_317);
if (lean_is_scalar(x_332)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_332;
}
lean_ctor_set(x_382, 0, x_339);
lean_ctor_set(x_382, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_320;
}
lean_ctor_set(x_383, 0, x_338);
lean_ctor_set(x_383, 1, x_382);
x_7 = x_13;
x_8 = x_383;
goto _start;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_333);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_321);
lean_ctor_set(x_385, 1, x_317);
if (lean_is_scalar(x_334)) {
 x_386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_386 = x_334;
}
lean_ctor_set(x_386, 0, x_331);
if (lean_is_scalar(x_332)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_332;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_320;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_387);
x_7 = x_13;
x_8 = x_388;
goto _start;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_390 = lean_ctor_get(x_8, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_391 = x_8;
} else {
 lean_dec_ref(x_8);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_15, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_15, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_394 = x_15;
} else {
 lean_dec_ref(x_15);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_316, 2);
lean_inc(x_395);
x_396 = lean_ctor_get(x_316, 3);
lean_inc(x_396);
x_397 = lean_ctor_get(x_316, 4);
lean_inc(x_397);
lean_dec(x_316);
x_398 = l_List_isEmpty___rarg(x_390);
lean_inc(x_2);
x_399 = l_Lean_MetavarContext_instantiateMVars(x_2, x_396);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec(x_399);
lean_inc(x_2);
x_401 = l_Lean_MetavarContext_instantiateMVars(x_2, x_397);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec(x_401);
x_403 = l_System_FilePath_dirName___closed__1;
x_404 = l_Lean_Name_toStringWithSep___main(x_403, x_395);
x_405 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_406 = 0;
x_407 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_408 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_409 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_400);
x_410 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*2, x_406);
x_411 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_412 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_413 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_402);
x_414 = lean_box(1);
x_415 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
lean_ctor_set_uint8(x_415, sizeof(void*)*2, x_406);
x_416 = lean_unsigned_to_nat(2u);
x_417 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
x_418 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_418, 0, x_412);
lean_ctor_set(x_418, 1, x_417);
lean_ctor_set_uint8(x_418, sizeof(void*)*2, x_406);
x_419 = lean_format_group(x_418);
x_420 = lean_box(0);
x_421 = lean_box(0);
if (x_398 == 0)
{
uint8_t x_434; 
x_434 = l_Lean_Format_isNil(x_393);
if (x_434 == 0)
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_435, 0, x_393);
lean_ctor_set(x_435, 1, x_414);
lean_ctor_set_uint8(x_435, sizeof(void*)*2, x_406);
if (lean_obj_tag(x_390) == 0)
{
lean_dec(x_392);
x_422 = x_435;
goto block_433;
}
else
{
if (lean_obj_tag(x_392) == 0)
{
lean_dec(x_390);
x_422 = x_435;
goto block_433;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_436 = lean_ctor_get(x_392, 0);
lean_inc(x_436);
lean_dec(x_392);
x_437 = l_List_reverse___rarg(x_390);
x_438 = l_Lean_Format_flatten___main___closed__1;
x_439 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_437, x_438);
x_440 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_441 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_442 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_436);
x_443 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_443, 0, x_414);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_406);
x_444 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_444, 0, x_416);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*2, x_406);
x_446 = lean_format_group(x_445);
x_447 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_447, 0, x_435);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_406);
x_422 = x_447;
goto block_433;
}
}
}
else
{
if (lean_obj_tag(x_390) == 0)
{
lean_dec(x_392);
x_422 = x_393;
goto block_433;
}
else
{
if (lean_obj_tag(x_392) == 0)
{
lean_dec(x_390);
x_422 = x_393;
goto block_433;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_448 = lean_ctor_get(x_392, 0);
lean_inc(x_448);
lean_dec(x_392);
x_449 = l_List_reverse___rarg(x_390);
x_450 = l_Lean_Format_flatten___main___closed__1;
x_451 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_449, x_450);
x_452 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_453 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
lean_ctor_set_uint8(x_453, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_454 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_448);
x_455 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_455, 0, x_414);
lean_ctor_set(x_455, 1, x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*2, x_406);
x_456 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_456, 0, x_416);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_457, 0, x_453);
lean_ctor_set(x_457, 1, x_456);
lean_ctor_set_uint8(x_457, sizeof(void*)*2, x_406);
x_458 = lean_format_group(x_457);
x_459 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_459, 0, x_393);
lean_ctor_set(x_459, 1, x_458);
lean_ctor_set_uint8(x_459, sizeof(void*)*2, x_406);
x_422 = x_459;
goto block_433;
}
}
}
}
else
{
lean_dec(x_392);
lean_dec(x_390);
x_422 = x_393;
goto block_433;
}
block_433:
{
uint8_t x_423; 
x_423 = l_Lean_Format_isNil(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_424 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_414);
lean_ctor_set_uint8(x_424, sizeof(void*)*2, x_406);
x_425 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_419);
lean_ctor_set_uint8(x_425, sizeof(void*)*2, x_406);
if (lean_is_scalar(x_394)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_394;
}
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_425);
if (lean_is_scalar(x_391)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_391;
}
lean_ctor_set(x_427, 0, x_420);
lean_ctor_set(x_427, 1, x_426);
x_7 = x_13;
x_8 = x_427;
goto _start;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_429, 0, x_422);
lean_ctor_set(x_429, 1, x_419);
lean_ctor_set_uint8(x_429, sizeof(void*)*2, x_406);
if (lean_is_scalar(x_394)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_394;
}
lean_ctor_set(x_430, 0, x_421);
lean_ctor_set(x_430, 1, x_429);
if (lean_is_scalar(x_391)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_391;
}
lean_ctor_set(x_431, 0, x_420);
lean_ctor_set(x_431, 1, x_430);
x_7 = x_13;
x_8 = x_431;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(x_1, x_2, x_3, x_4, x_7, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(x_1, x_2, x_3, x_4, x_10, x_10, x_11, x_6);
return x_12;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_2);
x_24 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_11, 0, x_26);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_28);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_11, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_15, 1, x_32);
lean_ctor_set(x_15, 0, x_31);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_11);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_expr_eqv(x_38, x_35);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_List_isEmpty___rarg(x_18);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_20, 0, x_35);
if (x_40 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Format_isNil(x_21);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_46);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = l_List_reverse___rarg(x_18);
x_49 = l_Lean_Format_flatten___main___closed__1;
x_50 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_48, x_49);
x_51 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_44);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_44);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_44);
x_58 = lean_format_group(x_57);
x_59 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_44);
lean_ctor_set(x_24, 1, x_59);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = l_List_reverse___rarg(x_18);
x_63 = l_Lean_Format_flatten___main___closed__1;
x_64 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_62, x_63);
x_65 = 0;
x_66 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_65);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_69 = lean_box(1);
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_65);
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_65);
x_74 = lean_format_group(x_73);
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_21);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_65);
lean_ctor_set(x_24, 1, x_75);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_78; 
lean_dec(x_38);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_22);
lean_ctor_set(x_78, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_78);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_20, 0);
lean_inc(x_80);
lean_dec(x_20);
x_81 = lean_expr_eqv(x_80, x_35);
if (x_81 == 0)
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = l_List_isEmpty___rarg(x_18);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_22);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_35);
if (x_82 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Format_isNil(x_21);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_89, 0, x_21);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_87);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_80);
lean_ctor_set(x_24, 1, x_89);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = l_List_reverse___rarg(x_18);
x_92 = l_Lean_Format_flatten___main___closed__1;
x_93 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_91, x_92);
x_94 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_95 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_87);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_96 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_80);
x_97 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_87);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_87);
x_101 = lean_format_group(x_100);
x_102 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_87);
lean_ctor_set(x_24, 1, x_102);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_80);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_105 = l_List_reverse___rarg(x_18);
x_106 = l_Lean_Format_flatten___main___closed__1;
x_107 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_105, x_106);
x_108 = 0;
x_109 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_108);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_111 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_80);
x_112 = lean_box(1);
x_113 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_108);
x_117 = lean_format_group(x_116);
x_118 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_118, 0, x_21);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_108);
lean_ctor_set(x_24, 1, x_118);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_80);
lean_dec(x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_85);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_84);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_80);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_22);
lean_ctor_set(x_121, 1, x_18);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_122);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_121);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_24, 0);
lean_inc(x_124);
lean_dec(x_24);
x_125 = lean_ctor_get(x_20, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_126 = x_20;
} else {
 lean_dec_ref(x_20);
 x_126 = lean_box(0);
}
x_127 = lean_expr_eqv(x_125, x_124);
if (x_127 == 0)
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = l_List_isEmpty___rarg(x_18);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_22);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_124);
if (x_128 == 0)
{
uint8_t x_132; 
x_132 = l_Lean_Format_isNil(x_21);
if (x_132 == 0)
{
uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_133 = 0;
x_134 = lean_box(1);
x_135 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_135, 0, x_21);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_133);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_136; 
lean_dec(x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_15, 1, x_136);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_138 = l_List_reverse___rarg(x_18);
x_139 = l_Lean_Format_flatten___main___closed__1;
x_140 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_138, x_139);
x_141 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_142 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_133);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_143 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_125);
x_144 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_133);
x_145 = lean_unsigned_to_nat(2u);
x_146 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_133);
x_148 = lean_format_group(x_147);
x_149 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*2, x_133);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_15, 1, x_150);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_152; 
lean_dec(x_125);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_131);
lean_ctor_set(x_152, 1, x_21);
lean_ctor_set(x_15, 1, x_152);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_154 = l_List_reverse___rarg(x_18);
x_155 = l_Lean_Format_flatten___main___closed__1;
x_156 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_154, x_155);
x_157 = 0;
x_158 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_159 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*2, x_157);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_160 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_125);
x_161 = lean_box(1);
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_157);
x_163 = lean_unsigned_to_nat(2u);
x_164 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_157);
x_166 = lean_format_group(x_165);
x_167 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_167, 0, x_21);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*2, x_157);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_131);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_15, 1, x_168);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_170; 
lean_dec(x_125);
lean_dec(x_18);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_131);
lean_ctor_set(x_170, 1, x_21);
lean_ctor_set(x_15, 1, x_170);
lean_ctor_set(x_15, 0, x_130);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_125);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_22);
lean_ctor_set(x_172, 1, x_18);
if (lean_is_scalar(x_126)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_126;
}
lean_ctor_set(x_173, 0, x_124);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_21);
lean_ctor_set(x_15, 1, x_174);
lean_ctor_set(x_15, 0, x_172);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_15, 0);
x_177 = lean_ctor_get(x_15, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_15);
x_178 = lean_ctor_get(x_17, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_17, 3);
lean_inc(x_179);
lean_dec(x_17);
lean_inc(x_2);
x_180 = l_Lean_MetavarContext_instantiateMVars(x_2, x_179);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_178);
lean_ctor_set(x_183, 1, x_18);
lean_ctor_set(x_11, 0, x_181);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_11);
lean_ctor_set(x_184, 1, x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_7 = x_13;
x_8 = x_185;
goto _start;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_free_object(x_11);
x_187 = lean_ctor_get(x_180, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_188 = x_180;
} else {
 lean_dec_ref(x_180);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_176, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_190 = x_176;
} else {
 lean_dec_ref(x_176);
 x_190 = lean_box(0);
}
x_191 = lean_expr_eqv(x_189, x_187);
if (x_191 == 0)
{
uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = l_List_isEmpty___rarg(x_18);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_178);
lean_ctor_set(x_194, 1, x_193);
if (lean_is_scalar(x_190)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_190;
}
lean_ctor_set(x_195, 0, x_187);
if (x_192 == 0)
{
uint8_t x_196; 
x_196 = l_Lean_Format_isNil(x_177);
if (x_196 == 0)
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; 
x_197 = 0;
x_198 = lean_box(1);
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_177);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_197);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_189);
if (lean_is_scalar(x_188)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_188;
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_200);
x_7 = x_13;
x_8 = x_201;
goto _start;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_203 = l_List_reverse___rarg(x_18);
x_204 = l_Lean_Format_flatten___main___closed__1;
x_205 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_203, x_204);
x_206 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_207 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*2, x_197);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_208 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_189);
x_209 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_209, 0, x_198);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_197);
x_210 = lean_unsigned_to_nat(2u);
x_211 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set_uint8(x_212, sizeof(void*)*2, x_197);
x_213 = lean_format_group(x_212);
x_214 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_214, 0, x_199);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_197);
if (lean_is_scalar(x_188)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_188;
}
lean_ctor_set(x_215, 0, x_195);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_194);
lean_ctor_set(x_216, 1, x_215);
x_7 = x_13;
x_8 = x_216;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_189);
if (lean_is_scalar(x_188)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_188;
}
lean_ctor_set(x_218, 0, x_195);
lean_ctor_set(x_218, 1, x_177);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_194);
lean_ctor_set(x_219, 1, x_218);
x_7 = x_13;
x_8 = x_219;
goto _start;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_221 = l_List_reverse___rarg(x_18);
x_222 = l_Lean_Format_flatten___main___closed__1;
x_223 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_221, x_222);
x_224 = 0;
x_225 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_226 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_224);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_227 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_189);
x_228 = lean_box(1);
x_229 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_224);
x_230 = lean_unsigned_to_nat(2u);
x_231 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_232, 0, x_226);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*2, x_224);
x_233 = lean_format_group(x_232);
x_234 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_234, 0, x_177);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*2, x_224);
if (lean_is_scalar(x_188)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_188;
}
lean_ctor_set(x_235, 0, x_195);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_194);
lean_ctor_set(x_236, 1, x_235);
x_7 = x_13;
x_8 = x_236;
goto _start;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_189);
lean_dec(x_18);
if (lean_is_scalar(x_188)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_188;
}
lean_ctor_set(x_238, 0, x_195);
lean_ctor_set(x_238, 1, x_177);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_194);
lean_ctor_set(x_239, 1, x_238);
x_7 = x_13;
x_8 = x_239;
goto _start;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_189);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_178);
lean_ctor_set(x_241, 1, x_18);
if (lean_is_scalar(x_190)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_190;
}
lean_ctor_set(x_242, 0, x_187);
if (lean_is_scalar(x_188)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_188;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_177);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
x_7 = x_13;
x_8 = x_244;
goto _start;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_free_object(x_11);
x_246 = lean_ctor_get(x_8, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_247 = x_8;
} else {
 lean_dec_ref(x_8);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_15, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_15, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_250 = x_15;
} else {
 lean_dec_ref(x_15);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_17, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_17, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_17, 4);
lean_inc(x_253);
lean_dec(x_17);
x_254 = l_List_isEmpty___rarg(x_246);
lean_inc(x_2);
x_255 = l_Lean_MetavarContext_instantiateMVars(x_2, x_252);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec(x_255);
lean_inc(x_2);
x_257 = l_Lean_MetavarContext_instantiateMVars(x_2, x_253);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_System_FilePath_dirName___closed__1;
x_260 = l_Lean_Name_toStringWithSep___main(x_259, x_251);
x_261 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = 0;
x_263 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_264 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set_uint8(x_264, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_265 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_256);
x_266 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set_uint8(x_266, sizeof(void*)*2, x_262);
x_267 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_268 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set_uint8(x_268, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_269 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_258);
x_270 = lean_box(1);
x_271 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*2, x_262);
x_272 = lean_unsigned_to_nat(2u);
x_273 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_268);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_262);
x_275 = lean_format_group(x_274);
x_276 = lean_box(0);
x_277 = lean_box(0);
if (x_254 == 0)
{
uint8_t x_290; 
x_290 = l_Lean_Format_isNil(x_249);
if (x_290 == 0)
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_291, 0, x_249);
lean_ctor_set(x_291, 1, x_270);
lean_ctor_set_uint8(x_291, sizeof(void*)*2, x_262);
if (lean_obj_tag(x_246) == 0)
{
lean_dec(x_248);
x_278 = x_291;
goto block_289;
}
else
{
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_246);
x_278 = x_291;
goto block_289;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_292 = lean_ctor_get(x_248, 0);
lean_inc(x_292);
lean_dec(x_248);
x_293 = l_List_reverse___rarg(x_246);
x_294 = l_Lean_Format_flatten___main___closed__1;
x_295 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_293, x_294);
x_296 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_297 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_298 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_292);
x_299 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_299, 0, x_270);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_262);
x_300 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_300, 0, x_272);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*2, x_262);
x_302 = lean_format_group(x_301);
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_291);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_262);
x_278 = x_303;
goto block_289;
}
}
}
else
{
if (lean_obj_tag(x_246) == 0)
{
lean_dec(x_248);
x_278 = x_249;
goto block_289;
}
else
{
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_246);
x_278 = x_249;
goto block_289;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_304 = lean_ctor_get(x_248, 0);
lean_inc(x_304);
lean_dec(x_248);
x_305 = l_List_reverse___rarg(x_246);
x_306 = l_Lean_Format_flatten___main___closed__1;
x_307 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_305, x_306);
x_308 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_309 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set_uint8(x_309, sizeof(void*)*2, x_262);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_310 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_304);
x_311 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_311, 0, x_270);
lean_ctor_set(x_311, 1, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*2, x_262);
x_312 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_312, 0, x_272);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*2, x_262);
x_314 = lean_format_group(x_313);
x_315 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_315, 0, x_249);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_uint8(x_315, sizeof(void*)*2, x_262);
x_278 = x_315;
goto block_289;
}
}
}
}
else
{
lean_dec(x_248);
lean_dec(x_246);
x_278 = x_249;
goto block_289;
}
block_289:
{
uint8_t x_279; 
x_279 = l_Lean_Format_isNil(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_270);
lean_ctor_set_uint8(x_280, sizeof(void*)*2, x_262);
x_281 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_275);
lean_ctor_set_uint8(x_281, sizeof(void*)*2, x_262);
if (lean_is_scalar(x_250)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_250;
}
lean_ctor_set(x_282, 0, x_277);
lean_ctor_set(x_282, 1, x_281);
if (lean_is_scalar(x_247)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_247;
}
lean_ctor_set(x_283, 0, x_276);
lean_ctor_set(x_283, 1, x_282);
x_7 = x_13;
x_8 = x_283;
goto _start;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_285, 0, x_278);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set_uint8(x_285, sizeof(void*)*2, x_262);
if (lean_is_scalar(x_250)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_250;
}
lean_ctor_set(x_286, 0, x_277);
lean_ctor_set(x_286, 1, x_285);
if (lean_is_scalar(x_247)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_247;
}
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_286);
x_7 = x_13;
x_8 = x_287;
goto _start;
}
}
}
}
else
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_11, 0);
lean_inc(x_316);
lean_dec(x_11);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_8, 0);
lean_inc(x_317);
lean_dec(x_8);
x_318 = lean_ctor_get(x_15, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_15, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_320 = x_15;
} else {
 lean_dec_ref(x_15);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_316, 2);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 3);
lean_inc(x_322);
lean_dec(x_316);
lean_inc(x_2);
x_323 = l_Lean_MetavarContext_instantiateMVars(x_2, x_322);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_321);
lean_ctor_set(x_326, 1, x_317);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_324);
if (lean_is_scalar(x_325)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_325;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_320;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_328);
x_7 = x_13;
x_8 = x_329;
goto _start;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_323, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_332 = x_323;
} else {
 lean_dec_ref(x_323);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_318, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_334 = x_318;
} else {
 lean_dec_ref(x_318);
 x_334 = lean_box(0);
}
x_335 = lean_expr_eqv(x_333, x_331);
if (x_335 == 0)
{
uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = l_List_isEmpty___rarg(x_317);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_321);
lean_ctor_set(x_338, 1, x_337);
if (lean_is_scalar(x_334)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_334;
}
lean_ctor_set(x_339, 0, x_331);
if (x_336 == 0)
{
uint8_t x_340; 
x_340 = l_Lean_Format_isNil(x_319);
if (x_340 == 0)
{
uint8_t x_341; lean_object* x_342; lean_object* x_343; 
x_341 = 0;
x_342 = lean_box(1);
x_343 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_343, 0, x_319);
lean_ctor_set(x_343, 1, x_342);
lean_ctor_set_uint8(x_343, sizeof(void*)*2, x_341);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_332;
}
lean_ctor_set(x_344, 0, x_339);
lean_ctor_set(x_344, 1, x_343);
if (lean_is_scalar(x_320)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_320;
}
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_344);
x_7 = x_13;
x_8 = x_345;
goto _start;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_347 = l_List_reverse___rarg(x_317);
x_348 = l_Lean_Format_flatten___main___closed__1;
x_349 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_347, x_348);
x_350 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_351 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*2, x_341);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_352 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_353 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*2, x_341);
x_354 = lean_unsigned_to_nat(2u);
x_355 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
x_356 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set_uint8(x_356, sizeof(void*)*2, x_341);
x_357 = lean_format_group(x_356);
x_358 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_358, 0, x_343);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*2, x_341);
if (lean_is_scalar(x_332)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_332;
}
lean_ctor_set(x_359, 0, x_339);
lean_ctor_set(x_359, 1, x_358);
if (lean_is_scalar(x_320)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_320;
}
lean_ctor_set(x_360, 0, x_338);
lean_ctor_set(x_360, 1, x_359);
x_7 = x_13;
x_8 = x_360;
goto _start;
}
}
else
{
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_332;
}
lean_ctor_set(x_362, 0, x_339);
lean_ctor_set(x_362, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_320;
}
lean_ctor_set(x_363, 0, x_338);
lean_ctor_set(x_363, 1, x_362);
x_7 = x_13;
x_8 = x_363;
goto _start;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_365 = l_List_reverse___rarg(x_317);
x_366 = l_Lean_Format_flatten___main___closed__1;
x_367 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_365, x_366);
x_368 = 0;
x_369 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_370 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*2, x_368);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_371 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_372 = lean_box(1);
x_373 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*2, x_368);
x_374 = lean_unsigned_to_nat(2u);
x_375 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_376, 0, x_370);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set_uint8(x_376, sizeof(void*)*2, x_368);
x_377 = lean_format_group(x_376);
x_378 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_378, 0, x_319);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*2, x_368);
if (lean_is_scalar(x_332)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_332;
}
lean_ctor_set(x_379, 0, x_339);
lean_ctor_set(x_379, 1, x_378);
if (lean_is_scalar(x_320)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_320;
}
lean_ctor_set(x_380, 0, x_338);
lean_ctor_set(x_380, 1, x_379);
x_7 = x_13;
x_8 = x_380;
goto _start;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_333);
lean_dec(x_317);
if (lean_is_scalar(x_332)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_332;
}
lean_ctor_set(x_382, 0, x_339);
lean_ctor_set(x_382, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_320;
}
lean_ctor_set(x_383, 0, x_338);
lean_ctor_set(x_383, 1, x_382);
x_7 = x_13;
x_8 = x_383;
goto _start;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_333);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_321);
lean_ctor_set(x_385, 1, x_317);
if (lean_is_scalar(x_334)) {
 x_386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_386 = x_334;
}
lean_ctor_set(x_386, 0, x_331);
if (lean_is_scalar(x_332)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_332;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_320;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_387);
x_7 = x_13;
x_8 = x_388;
goto _start;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_390 = lean_ctor_get(x_8, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_391 = x_8;
} else {
 lean_dec_ref(x_8);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_15, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_15, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_394 = x_15;
} else {
 lean_dec_ref(x_15);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_316, 2);
lean_inc(x_395);
x_396 = lean_ctor_get(x_316, 3);
lean_inc(x_396);
x_397 = lean_ctor_get(x_316, 4);
lean_inc(x_397);
lean_dec(x_316);
x_398 = l_List_isEmpty___rarg(x_390);
lean_inc(x_2);
x_399 = l_Lean_MetavarContext_instantiateMVars(x_2, x_396);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec(x_399);
lean_inc(x_2);
x_401 = l_Lean_MetavarContext_instantiateMVars(x_2, x_397);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec(x_401);
x_403 = l_System_FilePath_dirName___closed__1;
x_404 = l_Lean_Name_toStringWithSep___main(x_403, x_395);
x_405 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_406 = 0;
x_407 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_408 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_409 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_400);
x_410 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*2, x_406);
x_411 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_412 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_413 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_402);
x_414 = lean_box(1);
x_415 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
lean_ctor_set_uint8(x_415, sizeof(void*)*2, x_406);
x_416 = lean_unsigned_to_nat(2u);
x_417 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
x_418 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_418, 0, x_412);
lean_ctor_set(x_418, 1, x_417);
lean_ctor_set_uint8(x_418, sizeof(void*)*2, x_406);
x_419 = lean_format_group(x_418);
x_420 = lean_box(0);
x_421 = lean_box(0);
if (x_398 == 0)
{
uint8_t x_434; 
x_434 = l_Lean_Format_isNil(x_393);
if (x_434 == 0)
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_435, 0, x_393);
lean_ctor_set(x_435, 1, x_414);
lean_ctor_set_uint8(x_435, sizeof(void*)*2, x_406);
if (lean_obj_tag(x_390) == 0)
{
lean_dec(x_392);
x_422 = x_435;
goto block_433;
}
else
{
if (lean_obj_tag(x_392) == 0)
{
lean_dec(x_390);
x_422 = x_435;
goto block_433;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_436 = lean_ctor_get(x_392, 0);
lean_inc(x_436);
lean_dec(x_392);
x_437 = l_List_reverse___rarg(x_390);
x_438 = l_Lean_Format_flatten___main___closed__1;
x_439 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_437, x_438);
x_440 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_441 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_442 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_436);
x_443 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_443, 0, x_414);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_406);
x_444 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_444, 0, x_416);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*2, x_406);
x_446 = lean_format_group(x_445);
x_447 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_447, 0, x_435);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_406);
x_422 = x_447;
goto block_433;
}
}
}
else
{
if (lean_obj_tag(x_390) == 0)
{
lean_dec(x_392);
x_422 = x_393;
goto block_433;
}
else
{
if (lean_obj_tag(x_392) == 0)
{
lean_dec(x_390);
x_422 = x_393;
goto block_433;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_448 = lean_ctor_get(x_392, 0);
lean_inc(x_448);
lean_dec(x_392);
x_449 = l_List_reverse___rarg(x_390);
x_450 = l_Lean_Format_flatten___main___closed__1;
x_451 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_449, x_450);
x_452 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_453 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
lean_ctor_set_uint8(x_453, sizeof(void*)*2, x_406);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_454 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_448);
x_455 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_455, 0, x_414);
lean_ctor_set(x_455, 1, x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*2, x_406);
x_456 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_456, 0, x_416);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_457, 0, x_453);
lean_ctor_set(x_457, 1, x_456);
lean_ctor_set_uint8(x_457, sizeof(void*)*2, x_406);
x_458 = lean_format_group(x_457);
x_459 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_459, 0, x_393);
lean_ctor_set(x_459, 1, x_458);
lean_ctor_set_uint8(x_459, sizeof(void*)*2, x_406);
x_422 = x_459;
goto block_433;
}
}
}
}
else
{
lean_dec(x_392);
lean_dec(x_390);
x_422 = x_393;
goto block_433;
}
block_433:
{
uint8_t x_423; 
x_423 = l_Lean_Format_isNil(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_424 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_414);
lean_ctor_set_uint8(x_424, sizeof(void*)*2, x_406);
x_425 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_419);
lean_ctor_set_uint8(x_425, sizeof(void*)*2, x_406);
if (lean_is_scalar(x_394)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_394;
}
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_425);
if (lean_is_scalar(x_391)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_391;
}
lean_ctor_set(x_427, 0, x_420);
lean_ctor_set(x_427, 1, x_426);
x_7 = x_13;
x_8 = x_427;
goto _start;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_429, 0, x_422);
lean_ctor_set(x_429, 1, x_419);
lean_ctor_set_uint8(x_429, sizeof(void*)*2, x_406);
if (lean_is_scalar(x_394)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_394;
}
lean_ctor_set(x_430, 0, x_421);
lean_ctor_set(x_430, 1, x_429);
if (lean_is_scalar(x_391)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_391;
}
lean_ctor_set(x_431, 0, x_420);
lean_ctor_set(x_431, 1, x_430);
x_7 = x_13;
x_8 = x_431;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(x_1, x_2, x_3, x_4, x_7, x_6);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_Std_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_ppGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown goal");
return x_1;
}
}
lean_object* _init_l_Lean_ppGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ppGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ppGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ppGoal___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ppGoal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⊢");
return x_1;
}
}
lean_object* _init_l_Lean_ppGoal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ppGoal___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case ");
return x_1;
}
}
lean_object* _init_l_Lean_ppGoal___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_metavar_ctx_find_decl(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_ppGoal___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_ppGoal___closed__4;
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(x_1, x_2, x_3, x_8, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_List_isEmpty___rarg(x_12);
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
if (x_15 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Format_isNil(x_14);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_60);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_62;
goto block_58;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_62;
goto block_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
lean_dec(x_13);
x_64 = l_List_reverse___rarg(x_12);
x_65 = l_Lean_Format_flatten___main___closed__1;
x_66 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_64, x_65);
x_67 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_68 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_60);
x_69 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_63);
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_60);
x_71 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_71, 0, x_18);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_60);
x_73 = lean_format_group(x_72);
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_60);
x_21 = x_74;
goto block_58;
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_14;
goto block_58;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_14;
goto block_58;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_ctor_get(x_13, 0);
lean_inc(x_75);
lean_dec(x_13);
x_76 = l_List_reverse___rarg(x_12);
x_77 = l_Lean_Format_flatten___main___closed__1;
x_78 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_76, x_77);
x_79 = 0;
x_80 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_81 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_79);
x_82 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_75);
x_83 = lean_box(1);
x_84 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_79);
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_18);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_79);
x_87 = lean_format_group(x_86);
x_88 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_88, 0, x_14);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_79);
x_21 = x_88;
goto block_58;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_14;
goto block_58;
}
block_58:
{
uint8_t x_22; 
x_22 = l_Lean_Format_isNil(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = 0;
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_ppGoal___closed__6;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_flatten___main___closed__1;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_23);
x_30 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_23);
if (lean_obj_tag(x_20) == 0)
{
return x_30;
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_31 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
x_32 = l_System_FilePath_dirName___closed__1;
x_33 = l_Lean_Name_toStringWithSep___main(x_32, x_20);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_ppGoal___closed__8;
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_23);
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_23);
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_23);
return x_38;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = 0;
x_42 = l_Lean_ppGoal___closed__6;
x_43 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_41);
x_44 = l_Lean_Format_flatten___main___closed__1;
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_41);
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_41);
if (lean_obj_tag(x_20) == 0)
{
return x_46;
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_47 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_48 = l_System_FilePath_dirName___closed__1;
x_49 = l_Lean_Name_toStringWithSep___main(x_48, x_20);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_ppGoal___closed__8;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_41);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_41);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_41);
return x_55;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_ppGoal___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_PPExt(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_PPGoal(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6);
l_Lean_ppGoal___closed__1 = _init_l_Lean_ppGoal___closed__1();
lean_mark_persistent(l_Lean_ppGoal___closed__1);
l_Lean_ppGoal___closed__2 = _init_l_Lean_ppGoal___closed__2();
lean_mark_persistent(l_Lean_ppGoal___closed__2);
l_Lean_ppGoal___closed__3 = _init_l_Lean_ppGoal___closed__3();
lean_mark_persistent(l_Lean_ppGoal___closed__3);
l_Lean_ppGoal___closed__4 = _init_l_Lean_ppGoal___closed__4();
lean_mark_persistent(l_Lean_ppGoal___closed__4);
l_Lean_ppGoal___closed__5 = _init_l_Lean_ppGoal___closed__5();
lean_mark_persistent(l_Lean_ppGoal___closed__5);
l_Lean_ppGoal___closed__6 = _init_l_Lean_ppGoal___closed__6();
lean_mark_persistent(l_Lean_ppGoal___closed__6);
l_Lean_ppGoal___closed__7 = _init_l_Lean_ppGoal___closed__7();
lean_mark_persistent(l_Lean_ppGoal___closed__7);
l_Lean_ppGoal___closed__8 = _init_l_Lean_ppGoal___closed__8();
lean_mark_persistent(l_Lean_ppGoal___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
