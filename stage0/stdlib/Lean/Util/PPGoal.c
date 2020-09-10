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
lean_object* lean_simp_macro_scopes(lean_object*);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_simp_macro_scopes(x_22);
lean_inc(x_2);
x_25 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_dec(x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_29);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_11, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_32);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_11);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_expr_eqv(x_39, x_36);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = l_List_isEmpty___rarg(x_18);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_20, 0, x_36);
if (x_41 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Format_isNil(x_21);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_45);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_39);
lean_ctor_set(x_25, 1, x_47);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = l_List_reverse___rarg(x_18);
x_50 = l_Lean_Format_flatten___main___closed__1;
x_51 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_49, x_50);
x_52 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_45);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_39);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_45);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_45);
x_59 = lean_format_group(x_58);
x_60 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_45);
lean_ctor_set(x_25, 1, x_60);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_39);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = l_List_reverse___rarg(x_18);
x_64 = l_Lean_Format_flatten___main___closed__1;
x_65 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_63, x_64);
x_66 = 0;
x_67 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_68 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_66);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_39);
x_70 = lean_box(1);
x_71 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_66);
x_75 = lean_format_group(x_74);
x_76 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_66);
lean_ctor_set(x_25, 1, x_76);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_18);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_79; 
lean_dec(x_39);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_24);
lean_ctor_set(x_79, 1, x_18);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_79);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_20, 0);
lean_inc(x_81);
lean_dec(x_20);
x_82 = lean_expr_eqv(x_81, x_36);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = l_List_isEmpty___rarg(x_18);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_24);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_36);
if (x_83 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Format_isNil(x_21);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_88 = 0;
x_89 = lean_box(1);
x_90 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_90, 0, x_21);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_88);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_81);
lean_ctor_set(x_25, 1, x_90);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = l_List_reverse___rarg(x_18);
x_93 = l_Lean_Format_flatten___main___closed__1;
x_94 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_92, x_93);
x_95 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_96 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*2, x_88);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_97 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_81);
x_98 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_88);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_88);
x_102 = lean_format_group(x_101);
x_103 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_88);
lean_ctor_set(x_25, 1, x_103);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_81);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = l_List_reverse___rarg(x_18);
x_107 = l_Lean_Format_flatten___main___closed__1;
x_108 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_106, x_107);
x_109 = 0;
x_110 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_111 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_109);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_112 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_81);
x_113 = lean_box(1);
x_114 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_109);
x_115 = lean_unsigned_to_nat(2u);
x_116 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_109);
x_118 = lean_format_group(x_117);
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_21);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_109);
lean_ctor_set(x_25, 1, x_119);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_18);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_81);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_24);
lean_ctor_set(x_122, 1, x_18);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_36);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_123);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_25, 0);
lean_inc(x_125);
lean_dec(x_25);
x_126 = lean_ctor_get(x_20, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_127 = x_20;
} else {
 lean_dec_ref(x_20);
 x_127 = lean_box(0);
}
x_128 = lean_expr_eqv(x_126, x_125);
if (x_128 == 0)
{
uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = l_List_isEmpty___rarg(x_18);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_24);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_127)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_127;
}
lean_ctor_set(x_132, 0, x_125);
if (x_129 == 0)
{
uint8_t x_133; 
x_133 = l_Lean_Format_isNil(x_21);
if (x_133 == 0)
{
uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_134 = 0;
x_135 = lean_box(1);
x_136 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_136, 0, x_21);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_134);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_137; 
lean_dec(x_126);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_15, 1, x_137);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_139 = l_List_reverse___rarg(x_18);
x_140 = l_Lean_Format_flatten___main___closed__1;
x_141 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_139, x_140);
x_142 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_143 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_134);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_144 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_126);
x_145 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_134);
x_146 = lean_unsigned_to_nat(2u);
x_147 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_134);
x_149 = lean_format_group(x_148);
x_150 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_134);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_132);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_15, 1, x_151);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_153; 
lean_dec(x_126);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_132);
lean_ctor_set(x_153, 1, x_21);
lean_ctor_set(x_15, 1, x_153);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_155 = l_List_reverse___rarg(x_18);
x_156 = l_Lean_Format_flatten___main___closed__1;
x_157 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_155, x_156);
x_158 = 0;
x_159 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_160 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_158);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_161 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_126);
x_162 = lean_box(1);
x_163 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_158);
x_164 = lean_unsigned_to_nat(2u);
x_165 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_160);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_158);
x_167 = lean_format_group(x_166);
x_168 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_168, 0, x_21);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*2, x_158);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_132);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_15, 1, x_169);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_171; 
lean_dec(x_126);
lean_dec(x_18);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_132);
lean_ctor_set(x_171, 1, x_21);
lean_ctor_set(x_15, 1, x_171);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_126);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_24);
lean_ctor_set(x_173, 1, x_18);
if (lean_is_scalar(x_127)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_127;
}
lean_ctor_set(x_174, 0, x_125);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_21);
lean_ctor_set(x_15, 1, x_175);
lean_ctor_set(x_15, 0, x_173);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_15, 0);
x_178 = lean_ctor_get(x_15, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_15);
x_179 = lean_ctor_get(x_17, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_17, 3);
lean_inc(x_180);
lean_dec(x_17);
x_181 = lean_simp_macro_scopes(x_179);
lean_inc(x_2);
x_182 = l_Lean_MetavarContext_instantiateMVars(x_2, x_180);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_18);
lean_ctor_set(x_11, 0, x_183);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_11);
lean_ctor_set(x_186, 1, x_178);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_7 = x_13;
x_8 = x_187;
goto _start;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_free_object(x_11);
x_189 = lean_ctor_get(x_182, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_190 = x_182;
} else {
 lean_dec_ref(x_182);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_192 = x_177;
} else {
 lean_dec_ref(x_177);
 x_192 = lean_box(0);
}
x_193 = lean_expr_eqv(x_191, x_189);
if (x_193 == 0)
{
uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = l_List_isEmpty___rarg(x_18);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_181);
lean_ctor_set(x_196, 1, x_195);
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_189);
if (x_194 == 0)
{
uint8_t x_198; 
x_198 = l_Lean_Format_isNil(x_178);
if (x_198 == 0)
{
uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_199 = 0;
x_200 = lean_box(1);
x_201 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_201, 0, x_178);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_199);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_191);
if (lean_is_scalar(x_190)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_190;
}
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_202);
x_7 = x_13;
x_8 = x_203;
goto _start;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_205 = l_List_reverse___rarg(x_18);
x_206 = l_Lean_Format_flatten___main___closed__1;
x_207 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_205, x_206);
x_208 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_209 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_199);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_210 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_191);
x_211 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_211, 0, x_200);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set_uint8(x_211, sizeof(void*)*2, x_199);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_214, 0, x_209);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_199);
x_215 = lean_format_group(x_214);
x_216 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_216, 0, x_201);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_199);
if (lean_is_scalar(x_190)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_190;
}
lean_ctor_set(x_217, 0, x_197);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_196);
lean_ctor_set(x_218, 1, x_217);
x_7 = x_13;
x_8 = x_218;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_191);
if (lean_is_scalar(x_190)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_190;
}
lean_ctor_set(x_220, 0, x_197);
lean_ctor_set(x_220, 1, x_178);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_196);
lean_ctor_set(x_221, 1, x_220);
x_7 = x_13;
x_8 = x_221;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_223 = l_List_reverse___rarg(x_18);
x_224 = l_Lean_Format_flatten___main___closed__1;
x_225 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_223, x_224);
x_226 = 0;
x_227 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_228 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*2, x_226);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_229 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_191);
x_230 = lean_box(1);
x_231 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
lean_ctor_set_uint8(x_231, sizeof(void*)*2, x_226);
x_232 = lean_unsigned_to_nat(2u);
x_233 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_234, 0, x_228);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*2, x_226);
x_235 = lean_format_group(x_234);
x_236 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_236, 0, x_178);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_226);
if (lean_is_scalar(x_190)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_190;
}
lean_ctor_set(x_237, 0, x_197);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_196);
lean_ctor_set(x_238, 1, x_237);
x_7 = x_13;
x_8 = x_238;
goto _start;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_191);
lean_dec(x_18);
if (lean_is_scalar(x_190)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_190;
}
lean_ctor_set(x_240, 0, x_197);
lean_ctor_set(x_240, 1, x_178);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_196);
lean_ctor_set(x_241, 1, x_240);
x_7 = x_13;
x_8 = x_241;
goto _start;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_191);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_181);
lean_ctor_set(x_243, 1, x_18);
if (lean_is_scalar(x_192)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_192;
}
lean_ctor_set(x_244, 0, x_189);
if (lean_is_scalar(x_190)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_190;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_178);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_245);
x_7 = x_13;
x_8 = x_246;
goto _start;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_free_object(x_11);
x_248 = lean_ctor_get(x_8, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_249 = x_8;
} else {
 lean_dec_ref(x_8);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_15, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_15, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_252 = x_15;
} else {
 lean_dec_ref(x_15);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_17, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_17, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_17, 4);
lean_inc(x_255);
lean_dec(x_17);
x_256 = lean_simp_macro_scopes(x_253);
x_257 = l_List_isEmpty___rarg(x_248);
lean_inc(x_2);
x_258 = l_Lean_MetavarContext_instantiateMVars(x_2, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec(x_258);
lean_inc(x_2);
x_260 = l_Lean_MetavarContext_instantiateMVars(x_2, x_255);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l_System_FilePath_dirName___closed__1;
x_263 = l_Lean_Name_toStringWithSep___main(x_262, x_256);
x_264 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = 0;
x_266 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_267 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_268 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_259);
x_269 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_265);
x_270 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_271 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set_uint8(x_271, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_272 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_261);
x_273 = lean_box(1);
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_265);
x_275 = lean_unsigned_to_nat(2u);
x_276 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_277, 0, x_271);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set_uint8(x_277, sizeof(void*)*2, x_265);
x_278 = lean_format_group(x_277);
x_279 = lean_box(0);
x_280 = lean_box(0);
if (x_257 == 0)
{
uint8_t x_293; 
x_293 = l_Lean_Format_isNil(x_251);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_294, 0, x_251);
lean_ctor_set(x_294, 1, x_273);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_265);
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_250);
x_281 = x_294;
goto block_292;
}
else
{
if (lean_obj_tag(x_250) == 0)
{
lean_dec(x_248);
x_281 = x_294;
goto block_292;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_295 = lean_ctor_get(x_250, 0);
lean_inc(x_295);
lean_dec(x_250);
x_296 = l_List_reverse___rarg(x_248);
x_297 = l_Lean_Format_flatten___main___closed__1;
x_298 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_296, x_297);
x_299 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_300 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_301 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_295);
x_302 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_302, 0, x_273);
lean_ctor_set(x_302, 1, x_301);
lean_ctor_set_uint8(x_302, sizeof(void*)*2, x_265);
x_303 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_303, 0, x_275);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_265);
x_305 = lean_format_group(x_304);
x_306 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_306, 0, x_294);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set_uint8(x_306, sizeof(void*)*2, x_265);
x_281 = x_306;
goto block_292;
}
}
}
else
{
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_250);
x_281 = x_251;
goto block_292;
}
else
{
if (lean_obj_tag(x_250) == 0)
{
lean_dec(x_248);
x_281 = x_251;
goto block_292;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_250, 0);
lean_inc(x_307);
lean_dec(x_250);
x_308 = l_List_reverse___rarg(x_248);
x_309 = l_Lean_Format_flatten___main___closed__1;
x_310 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_308, x_309);
x_311 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_312 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set_uint8(x_312, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_313 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_307);
x_314 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_314, 0, x_273);
lean_ctor_set(x_314, 1, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*2, x_265);
x_315 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_315, 0, x_275);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_316, 0, x_312);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*2, x_265);
x_317 = lean_format_group(x_316);
x_318 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_318, 0, x_251);
lean_ctor_set(x_318, 1, x_317);
lean_ctor_set_uint8(x_318, sizeof(void*)*2, x_265);
x_281 = x_318;
goto block_292;
}
}
}
}
else
{
lean_dec(x_250);
lean_dec(x_248);
x_281 = x_251;
goto block_292;
}
block_292:
{
uint8_t x_282; 
x_282 = l_Lean_Format_isNil(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_265);
x_284 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*2, x_265);
if (lean_is_scalar(x_252)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_252;
}
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_284);
if (lean_is_scalar(x_249)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_249;
}
lean_ctor_set(x_286, 0, x_279);
lean_ctor_set(x_286, 1, x_285);
x_7 = x_13;
x_8 = x_286;
goto _start;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_288, 0, x_281);
lean_ctor_set(x_288, 1, x_278);
lean_ctor_set_uint8(x_288, sizeof(void*)*2, x_265);
if (lean_is_scalar(x_252)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_252;
}
lean_ctor_set(x_289, 0, x_280);
lean_ctor_set(x_289, 1, x_288);
if (lean_is_scalar(x_249)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_249;
}
lean_ctor_set(x_290, 0, x_279);
lean_ctor_set(x_290, 1, x_289);
x_7 = x_13;
x_8 = x_290;
goto _start;
}
}
}
}
else
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_11, 0);
lean_inc(x_319);
lean_dec(x_11);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_320 = lean_ctor_get(x_8, 0);
lean_inc(x_320);
lean_dec(x_8);
x_321 = lean_ctor_get(x_15, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_15, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_323 = x_15;
} else {
 lean_dec_ref(x_15);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_319, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 3);
lean_inc(x_325);
lean_dec(x_319);
x_326 = lean_simp_macro_scopes(x_324);
lean_inc(x_2);
x_327 = l_Lean_MetavarContext_instantiateMVars(x_2, x_325);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_329 = x_327;
} else {
 lean_dec_ref(x_327);
 x_329 = lean_box(0);
}
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_320);
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_328);
if (lean_is_scalar(x_329)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_329;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_323;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_332);
x_7 = x_13;
x_8 = x_333;
goto _start;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_335 = lean_ctor_get(x_327, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_336 = x_327;
} else {
 lean_dec_ref(x_327);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_321, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_338 = x_321;
} else {
 lean_dec_ref(x_321);
 x_338 = lean_box(0);
}
x_339 = lean_expr_eqv(x_337, x_335);
if (x_339 == 0)
{
uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = l_List_isEmpty___rarg(x_320);
x_341 = lean_box(0);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_326);
lean_ctor_set(x_342, 1, x_341);
if (lean_is_scalar(x_338)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_338;
}
lean_ctor_set(x_343, 0, x_335);
if (x_340 == 0)
{
uint8_t x_344; 
x_344 = l_Lean_Format_isNil(x_322);
if (x_344 == 0)
{
uint8_t x_345; lean_object* x_346; lean_object* x_347; 
x_345 = 0;
x_346 = lean_box(1);
x_347 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_347, 0, x_322);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*2, x_345);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_337);
if (lean_is_scalar(x_336)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_336;
}
lean_ctor_set(x_348, 0, x_343);
lean_ctor_set(x_348, 1, x_347);
if (lean_is_scalar(x_323)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_323;
}
lean_ctor_set(x_349, 0, x_342);
lean_ctor_set(x_349, 1, x_348);
x_7 = x_13;
x_8 = x_349;
goto _start;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_351 = l_List_reverse___rarg(x_320);
x_352 = l_Lean_Format_flatten___main___closed__1;
x_353 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_351, x_352);
x_354 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_355 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set_uint8(x_355, sizeof(void*)*2, x_345);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_356 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_337);
x_357 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_357, 0, x_346);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*2, x_345);
x_358 = lean_unsigned_to_nat(2u);
x_359 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set_uint8(x_360, sizeof(void*)*2, x_345);
x_361 = lean_format_group(x_360);
x_362 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_362, 0, x_347);
lean_ctor_set(x_362, 1, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*2, x_345);
if (lean_is_scalar(x_336)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_336;
}
lean_ctor_set(x_363, 0, x_343);
lean_ctor_set(x_363, 1, x_362);
if (lean_is_scalar(x_323)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_323;
}
lean_ctor_set(x_364, 0, x_342);
lean_ctor_set(x_364, 1, x_363);
x_7 = x_13;
x_8 = x_364;
goto _start;
}
}
else
{
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_337);
if (lean_is_scalar(x_336)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_336;
}
lean_ctor_set(x_366, 0, x_343);
lean_ctor_set(x_366, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_323;
}
lean_ctor_set(x_367, 0, x_342);
lean_ctor_set(x_367, 1, x_366);
x_7 = x_13;
x_8 = x_367;
goto _start;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_369 = l_List_reverse___rarg(x_320);
x_370 = l_Lean_Format_flatten___main___closed__1;
x_371 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_369, x_370);
x_372 = 0;
x_373 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_374 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*2, x_372);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_375 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_337);
x_376 = lean_box(1);
x_377 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
lean_ctor_set_uint8(x_377, sizeof(void*)*2, x_372);
x_378 = lean_unsigned_to_nat(2u);
x_379 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_380, 0, x_374);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*2, x_372);
x_381 = lean_format_group(x_380);
x_382 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_382, 0, x_322);
lean_ctor_set(x_382, 1, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*2, x_372);
if (lean_is_scalar(x_336)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_336;
}
lean_ctor_set(x_383, 0, x_343);
lean_ctor_set(x_383, 1, x_382);
if (lean_is_scalar(x_323)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_323;
}
lean_ctor_set(x_384, 0, x_342);
lean_ctor_set(x_384, 1, x_383);
x_7 = x_13;
x_8 = x_384;
goto _start;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_337);
lean_dec(x_320);
if (lean_is_scalar(x_336)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_336;
}
lean_ctor_set(x_386, 0, x_343);
lean_ctor_set(x_386, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_323;
}
lean_ctor_set(x_387, 0, x_342);
lean_ctor_set(x_387, 1, x_386);
x_7 = x_13;
x_8 = x_387;
goto _start;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_337);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_326);
lean_ctor_set(x_389, 1, x_320);
if (lean_is_scalar(x_338)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_338;
}
lean_ctor_set(x_390, 0, x_335);
if (lean_is_scalar(x_336)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_336;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_323;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_391);
x_7 = x_13;
x_8 = x_392;
goto _start;
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_394 = lean_ctor_get(x_8, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_395 = x_8;
} else {
 lean_dec_ref(x_8);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_15, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_15, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_398 = x_15;
} else {
 lean_dec_ref(x_15);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_319, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_319, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_319, 4);
lean_inc(x_401);
lean_dec(x_319);
x_402 = lean_simp_macro_scopes(x_399);
x_403 = l_List_isEmpty___rarg(x_394);
lean_inc(x_2);
x_404 = l_Lean_MetavarContext_instantiateMVars(x_2, x_400);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec(x_404);
lean_inc(x_2);
x_406 = l_Lean_MetavarContext_instantiateMVars(x_2, x_401);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec(x_406);
x_408 = l_System_FilePath_dirName___closed__1;
x_409 = l_Lean_Name_toStringWithSep___main(x_408, x_402);
x_410 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_411 = 0;
x_412 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_413 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_412);
lean_ctor_set_uint8(x_413, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_414 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_405);
x_415 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*2, x_411);
x_416 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_417 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set_uint8(x_417, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_418 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_407);
x_419 = lean_box(1);
x_420 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*2, x_411);
x_421 = lean_unsigned_to_nat(2u);
x_422 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_420);
x_423 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_423, 0, x_417);
lean_ctor_set(x_423, 1, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*2, x_411);
x_424 = lean_format_group(x_423);
x_425 = lean_box(0);
x_426 = lean_box(0);
if (x_403 == 0)
{
uint8_t x_439; 
x_439 = l_Lean_Format_isNil(x_397);
if (x_439 == 0)
{
lean_object* x_440; 
x_440 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_440, 0, x_397);
lean_ctor_set(x_440, 1, x_419);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_411);
if (lean_obj_tag(x_394) == 0)
{
lean_dec(x_396);
x_427 = x_440;
goto block_438;
}
else
{
if (lean_obj_tag(x_396) == 0)
{
lean_dec(x_394);
x_427 = x_440;
goto block_438;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_441 = lean_ctor_get(x_396, 0);
lean_inc(x_441);
lean_dec(x_396);
x_442 = l_List_reverse___rarg(x_394);
x_443 = l_Lean_Format_flatten___main___closed__1;
x_444 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_442, x_443);
x_445 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_446 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set_uint8(x_446, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_447 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_441);
x_448 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_448, 0, x_419);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set_uint8(x_448, sizeof(void*)*2, x_411);
x_449 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_449, 0, x_421);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_450, 0, x_446);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*2, x_411);
x_451 = lean_format_group(x_450);
x_452 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_452, 0, x_440);
lean_ctor_set(x_452, 1, x_451);
lean_ctor_set_uint8(x_452, sizeof(void*)*2, x_411);
x_427 = x_452;
goto block_438;
}
}
}
else
{
if (lean_obj_tag(x_394) == 0)
{
lean_dec(x_396);
x_427 = x_397;
goto block_438;
}
else
{
if (lean_obj_tag(x_396) == 0)
{
lean_dec(x_394);
x_427 = x_397;
goto block_438;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_453 = lean_ctor_get(x_396, 0);
lean_inc(x_453);
lean_dec(x_396);
x_454 = l_List_reverse___rarg(x_394);
x_455 = l_Lean_Format_flatten___main___closed__1;
x_456 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_454, x_455);
x_457 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_458 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_459 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_453);
x_460 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_460, 0, x_419);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set_uint8(x_460, sizeof(void*)*2, x_411);
x_461 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_461, 0, x_421);
lean_ctor_set(x_461, 1, x_460);
x_462 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_462, 0, x_458);
lean_ctor_set(x_462, 1, x_461);
lean_ctor_set_uint8(x_462, sizeof(void*)*2, x_411);
x_463 = lean_format_group(x_462);
x_464 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_464, 0, x_397);
lean_ctor_set(x_464, 1, x_463);
lean_ctor_set_uint8(x_464, sizeof(void*)*2, x_411);
x_427 = x_464;
goto block_438;
}
}
}
}
else
{
lean_dec(x_396);
lean_dec(x_394);
x_427 = x_397;
goto block_438;
}
block_438:
{
uint8_t x_428; 
x_428 = l_Lean_Format_isNil(x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_419);
lean_ctor_set_uint8(x_429, sizeof(void*)*2, x_411);
x_430 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_424);
lean_ctor_set_uint8(x_430, sizeof(void*)*2, x_411);
if (lean_is_scalar(x_398)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_398;
}
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_430);
if (lean_is_scalar(x_395)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_395;
}
lean_ctor_set(x_432, 0, x_425);
lean_ctor_set(x_432, 1, x_431);
x_7 = x_13;
x_8 = x_432;
goto _start;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_434, 0, x_427);
lean_ctor_set(x_434, 1, x_424);
lean_ctor_set_uint8(x_434, sizeof(void*)*2, x_411);
if (lean_is_scalar(x_398)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_398;
}
lean_ctor_set(x_435, 0, x_426);
lean_ctor_set(x_435, 1, x_434);
if (lean_is_scalar(x_395)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_395;
}
lean_ctor_set(x_436, 0, x_425);
lean_ctor_set(x_436, 1, x_435);
x_7 = x_13;
x_8 = x_436;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_simp_macro_scopes(x_22);
lean_inc(x_2);
x_25 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_dec(x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_29);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_11, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_32);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_11);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_expr_eqv(x_39, x_36);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = l_List_isEmpty___rarg(x_18);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_20, 0, x_36);
if (x_41 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Format_isNil(x_21);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_45);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_39);
lean_ctor_set(x_25, 1, x_47);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = l_List_reverse___rarg(x_18);
x_50 = l_Lean_Format_flatten___main___closed__1;
x_51 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_49, x_50);
x_52 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_45);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_39);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_45);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_45);
x_59 = lean_format_group(x_58);
x_60 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_45);
lean_ctor_set(x_25, 1, x_60);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_39);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = l_List_reverse___rarg(x_18);
x_64 = l_Lean_Format_flatten___main___closed__1;
x_65 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_63, x_64);
x_66 = 0;
x_67 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_68 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_66);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_39);
x_70 = lean_box(1);
x_71 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_66);
x_75 = lean_format_group(x_74);
x_76 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_66);
lean_ctor_set(x_25, 1, x_76);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_18);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_43);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_79; 
lean_dec(x_39);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_24);
lean_ctor_set(x_79, 1, x_18);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_79);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_20, 0);
lean_inc(x_81);
lean_dec(x_20);
x_82 = lean_expr_eqv(x_81, x_36);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = l_List_isEmpty___rarg(x_18);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_24);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_36);
if (x_83 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Format_isNil(x_21);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_88 = 0;
x_89 = lean_box(1);
x_90 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_90, 0, x_21);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_88);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_81);
lean_ctor_set(x_25, 1, x_90);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = l_List_reverse___rarg(x_18);
x_93 = l_Lean_Format_flatten___main___closed__1;
x_94 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_92, x_93);
x_95 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_96 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*2, x_88);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_97 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_81);
x_98 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_88);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_88);
x_102 = lean_format_group(x_101);
x_103 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_88);
lean_ctor_set(x_25, 1, x_103);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_81);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = l_List_reverse___rarg(x_18);
x_107 = l_Lean_Format_flatten___main___closed__1;
x_108 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_106, x_107);
x_109 = 0;
x_110 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_111 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_109);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_112 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_81);
x_113 = lean_box(1);
x_114 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_109);
x_115 = lean_unsigned_to_nat(2u);
x_116 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_109);
x_118 = lean_format_group(x_117);
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_21);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_109);
lean_ctor_set(x_25, 1, x_119);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_18);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_86);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_85);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_81);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_24);
lean_ctor_set(x_122, 1, x_18);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_36);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_123);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_25, 0);
lean_inc(x_125);
lean_dec(x_25);
x_126 = lean_ctor_get(x_20, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_127 = x_20;
} else {
 lean_dec_ref(x_20);
 x_127 = lean_box(0);
}
x_128 = lean_expr_eqv(x_126, x_125);
if (x_128 == 0)
{
uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = l_List_isEmpty___rarg(x_18);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_24);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_127)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_127;
}
lean_ctor_set(x_132, 0, x_125);
if (x_129 == 0)
{
uint8_t x_133; 
x_133 = l_Lean_Format_isNil(x_21);
if (x_133 == 0)
{
uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_134 = 0;
x_135 = lean_box(1);
x_136 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_136, 0, x_21);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_134);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_137; 
lean_dec(x_126);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_15, 1, x_137);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_139 = l_List_reverse___rarg(x_18);
x_140 = l_Lean_Format_flatten___main___closed__1;
x_141 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_139, x_140);
x_142 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_143 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_134);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_144 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_126);
x_145 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_134);
x_146 = lean_unsigned_to_nat(2u);
x_147 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_134);
x_149 = lean_format_group(x_148);
x_150 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_134);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_132);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_15, 1, x_151);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_153; 
lean_dec(x_126);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_132);
lean_ctor_set(x_153, 1, x_21);
lean_ctor_set(x_15, 1, x_153);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_155 = l_List_reverse___rarg(x_18);
x_156 = l_Lean_Format_flatten___main___closed__1;
x_157 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_155, x_156);
x_158 = 0;
x_159 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_160 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_158);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_161 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_126);
x_162 = lean_box(1);
x_163 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_158);
x_164 = lean_unsigned_to_nat(2u);
x_165 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_160);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_158);
x_167 = lean_format_group(x_166);
x_168 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_168, 0, x_21);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*2, x_158);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_132);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_15, 1, x_169);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_171; 
lean_dec(x_126);
lean_dec(x_18);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_132);
lean_ctor_set(x_171, 1, x_21);
lean_ctor_set(x_15, 1, x_171);
lean_ctor_set(x_15, 0, x_131);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_126);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_24);
lean_ctor_set(x_173, 1, x_18);
if (lean_is_scalar(x_127)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_127;
}
lean_ctor_set(x_174, 0, x_125);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_21);
lean_ctor_set(x_15, 1, x_175);
lean_ctor_set(x_15, 0, x_173);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_15, 0);
x_178 = lean_ctor_get(x_15, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_15);
x_179 = lean_ctor_get(x_17, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_17, 3);
lean_inc(x_180);
lean_dec(x_17);
x_181 = lean_simp_macro_scopes(x_179);
lean_inc(x_2);
x_182 = l_Lean_MetavarContext_instantiateMVars(x_2, x_180);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_18);
lean_ctor_set(x_11, 0, x_183);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_11);
lean_ctor_set(x_186, 1, x_178);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_7 = x_13;
x_8 = x_187;
goto _start;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_free_object(x_11);
x_189 = lean_ctor_get(x_182, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_190 = x_182;
} else {
 lean_dec_ref(x_182);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_192 = x_177;
} else {
 lean_dec_ref(x_177);
 x_192 = lean_box(0);
}
x_193 = lean_expr_eqv(x_191, x_189);
if (x_193 == 0)
{
uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = l_List_isEmpty___rarg(x_18);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_181);
lean_ctor_set(x_196, 1, x_195);
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_189);
if (x_194 == 0)
{
uint8_t x_198; 
x_198 = l_Lean_Format_isNil(x_178);
if (x_198 == 0)
{
uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_199 = 0;
x_200 = lean_box(1);
x_201 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_201, 0, x_178);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_199);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_191);
if (lean_is_scalar(x_190)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_190;
}
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_202);
x_7 = x_13;
x_8 = x_203;
goto _start;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_205 = l_List_reverse___rarg(x_18);
x_206 = l_Lean_Format_flatten___main___closed__1;
x_207 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_205, x_206);
x_208 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_209 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_199);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_210 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_191);
x_211 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_211, 0, x_200);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set_uint8(x_211, sizeof(void*)*2, x_199);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_214, 0, x_209);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_199);
x_215 = lean_format_group(x_214);
x_216 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_216, 0, x_201);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_199);
if (lean_is_scalar(x_190)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_190;
}
lean_ctor_set(x_217, 0, x_197);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_196);
lean_ctor_set(x_218, 1, x_217);
x_7 = x_13;
x_8 = x_218;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_191);
if (lean_is_scalar(x_190)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_190;
}
lean_ctor_set(x_220, 0, x_197);
lean_ctor_set(x_220, 1, x_178);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_196);
lean_ctor_set(x_221, 1, x_220);
x_7 = x_13;
x_8 = x_221;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_223 = l_List_reverse___rarg(x_18);
x_224 = l_Lean_Format_flatten___main___closed__1;
x_225 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_223, x_224);
x_226 = 0;
x_227 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_228 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*2, x_226);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_229 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_191);
x_230 = lean_box(1);
x_231 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
lean_ctor_set_uint8(x_231, sizeof(void*)*2, x_226);
x_232 = lean_unsigned_to_nat(2u);
x_233 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_234, 0, x_228);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*2, x_226);
x_235 = lean_format_group(x_234);
x_236 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_236, 0, x_178);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_226);
if (lean_is_scalar(x_190)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_190;
}
lean_ctor_set(x_237, 0, x_197);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_196);
lean_ctor_set(x_238, 1, x_237);
x_7 = x_13;
x_8 = x_238;
goto _start;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_191);
lean_dec(x_18);
if (lean_is_scalar(x_190)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_190;
}
lean_ctor_set(x_240, 0, x_197);
lean_ctor_set(x_240, 1, x_178);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_196);
lean_ctor_set(x_241, 1, x_240);
x_7 = x_13;
x_8 = x_241;
goto _start;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_191);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_181);
lean_ctor_set(x_243, 1, x_18);
if (lean_is_scalar(x_192)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_192;
}
lean_ctor_set(x_244, 0, x_189);
if (lean_is_scalar(x_190)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_190;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_178);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_245);
x_7 = x_13;
x_8 = x_246;
goto _start;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_free_object(x_11);
x_248 = lean_ctor_get(x_8, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_249 = x_8;
} else {
 lean_dec_ref(x_8);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_15, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_15, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_252 = x_15;
} else {
 lean_dec_ref(x_15);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_17, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_17, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_17, 4);
lean_inc(x_255);
lean_dec(x_17);
x_256 = lean_simp_macro_scopes(x_253);
x_257 = l_List_isEmpty___rarg(x_248);
lean_inc(x_2);
x_258 = l_Lean_MetavarContext_instantiateMVars(x_2, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec(x_258);
lean_inc(x_2);
x_260 = l_Lean_MetavarContext_instantiateMVars(x_2, x_255);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l_System_FilePath_dirName___closed__1;
x_263 = l_Lean_Name_toStringWithSep___main(x_262, x_256);
x_264 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = 0;
x_266 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_267 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_268 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_259);
x_269 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_265);
x_270 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_271 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set_uint8(x_271, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_272 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_261);
x_273 = lean_box(1);
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_265);
x_275 = lean_unsigned_to_nat(2u);
x_276 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_277, 0, x_271);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set_uint8(x_277, sizeof(void*)*2, x_265);
x_278 = lean_format_group(x_277);
x_279 = lean_box(0);
x_280 = lean_box(0);
if (x_257 == 0)
{
uint8_t x_293; 
x_293 = l_Lean_Format_isNil(x_251);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_294, 0, x_251);
lean_ctor_set(x_294, 1, x_273);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_265);
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_250);
x_281 = x_294;
goto block_292;
}
else
{
if (lean_obj_tag(x_250) == 0)
{
lean_dec(x_248);
x_281 = x_294;
goto block_292;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_295 = lean_ctor_get(x_250, 0);
lean_inc(x_295);
lean_dec(x_250);
x_296 = l_List_reverse___rarg(x_248);
x_297 = l_Lean_Format_flatten___main___closed__1;
x_298 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_296, x_297);
x_299 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_300 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_301 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_295);
x_302 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_302, 0, x_273);
lean_ctor_set(x_302, 1, x_301);
lean_ctor_set_uint8(x_302, sizeof(void*)*2, x_265);
x_303 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_303, 0, x_275);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_265);
x_305 = lean_format_group(x_304);
x_306 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_306, 0, x_294);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set_uint8(x_306, sizeof(void*)*2, x_265);
x_281 = x_306;
goto block_292;
}
}
}
else
{
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_250);
x_281 = x_251;
goto block_292;
}
else
{
if (lean_obj_tag(x_250) == 0)
{
lean_dec(x_248);
x_281 = x_251;
goto block_292;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_250, 0);
lean_inc(x_307);
lean_dec(x_250);
x_308 = l_List_reverse___rarg(x_248);
x_309 = l_Lean_Format_flatten___main___closed__1;
x_310 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_308, x_309);
x_311 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_312 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set_uint8(x_312, sizeof(void*)*2, x_265);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_313 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_307);
x_314 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_314, 0, x_273);
lean_ctor_set(x_314, 1, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*2, x_265);
x_315 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_315, 0, x_275);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_316, 0, x_312);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*2, x_265);
x_317 = lean_format_group(x_316);
x_318 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_318, 0, x_251);
lean_ctor_set(x_318, 1, x_317);
lean_ctor_set_uint8(x_318, sizeof(void*)*2, x_265);
x_281 = x_318;
goto block_292;
}
}
}
}
else
{
lean_dec(x_250);
lean_dec(x_248);
x_281 = x_251;
goto block_292;
}
block_292:
{
uint8_t x_282; 
x_282 = l_Lean_Format_isNil(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_265);
x_284 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*2, x_265);
if (lean_is_scalar(x_252)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_252;
}
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_284);
if (lean_is_scalar(x_249)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_249;
}
lean_ctor_set(x_286, 0, x_279);
lean_ctor_set(x_286, 1, x_285);
x_7 = x_13;
x_8 = x_286;
goto _start;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_288, 0, x_281);
lean_ctor_set(x_288, 1, x_278);
lean_ctor_set_uint8(x_288, sizeof(void*)*2, x_265);
if (lean_is_scalar(x_252)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_252;
}
lean_ctor_set(x_289, 0, x_280);
lean_ctor_set(x_289, 1, x_288);
if (lean_is_scalar(x_249)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_249;
}
lean_ctor_set(x_290, 0, x_279);
lean_ctor_set(x_290, 1, x_289);
x_7 = x_13;
x_8 = x_290;
goto _start;
}
}
}
}
else
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_11, 0);
lean_inc(x_319);
lean_dec(x_11);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_320 = lean_ctor_get(x_8, 0);
lean_inc(x_320);
lean_dec(x_8);
x_321 = lean_ctor_get(x_15, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_15, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_323 = x_15;
} else {
 lean_dec_ref(x_15);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_319, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 3);
lean_inc(x_325);
lean_dec(x_319);
x_326 = lean_simp_macro_scopes(x_324);
lean_inc(x_2);
x_327 = l_Lean_MetavarContext_instantiateMVars(x_2, x_325);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_329 = x_327;
} else {
 lean_dec_ref(x_327);
 x_329 = lean_box(0);
}
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_320);
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_328);
if (lean_is_scalar(x_329)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_329;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_323;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_332);
x_7 = x_13;
x_8 = x_333;
goto _start;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_335 = lean_ctor_get(x_327, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_336 = x_327;
} else {
 lean_dec_ref(x_327);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_321, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_338 = x_321;
} else {
 lean_dec_ref(x_321);
 x_338 = lean_box(0);
}
x_339 = lean_expr_eqv(x_337, x_335);
if (x_339 == 0)
{
uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = l_List_isEmpty___rarg(x_320);
x_341 = lean_box(0);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_326);
lean_ctor_set(x_342, 1, x_341);
if (lean_is_scalar(x_338)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_338;
}
lean_ctor_set(x_343, 0, x_335);
if (x_340 == 0)
{
uint8_t x_344; 
x_344 = l_Lean_Format_isNil(x_322);
if (x_344 == 0)
{
uint8_t x_345; lean_object* x_346; lean_object* x_347; 
x_345 = 0;
x_346 = lean_box(1);
x_347 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_347, 0, x_322);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*2, x_345);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_337);
if (lean_is_scalar(x_336)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_336;
}
lean_ctor_set(x_348, 0, x_343);
lean_ctor_set(x_348, 1, x_347);
if (lean_is_scalar(x_323)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_323;
}
lean_ctor_set(x_349, 0, x_342);
lean_ctor_set(x_349, 1, x_348);
x_7 = x_13;
x_8 = x_349;
goto _start;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_351 = l_List_reverse___rarg(x_320);
x_352 = l_Lean_Format_flatten___main___closed__1;
x_353 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_351, x_352);
x_354 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_355 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set_uint8(x_355, sizeof(void*)*2, x_345);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_356 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_337);
x_357 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_357, 0, x_346);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*2, x_345);
x_358 = lean_unsigned_to_nat(2u);
x_359 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set_uint8(x_360, sizeof(void*)*2, x_345);
x_361 = lean_format_group(x_360);
x_362 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_362, 0, x_347);
lean_ctor_set(x_362, 1, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*2, x_345);
if (lean_is_scalar(x_336)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_336;
}
lean_ctor_set(x_363, 0, x_343);
lean_ctor_set(x_363, 1, x_362);
if (lean_is_scalar(x_323)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_323;
}
lean_ctor_set(x_364, 0, x_342);
lean_ctor_set(x_364, 1, x_363);
x_7 = x_13;
x_8 = x_364;
goto _start;
}
}
else
{
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_337);
if (lean_is_scalar(x_336)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_336;
}
lean_ctor_set(x_366, 0, x_343);
lean_ctor_set(x_366, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_323;
}
lean_ctor_set(x_367, 0, x_342);
lean_ctor_set(x_367, 1, x_366);
x_7 = x_13;
x_8 = x_367;
goto _start;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_369 = l_List_reverse___rarg(x_320);
x_370 = l_Lean_Format_flatten___main___closed__1;
x_371 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_369, x_370);
x_372 = 0;
x_373 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_374 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*2, x_372);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_375 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_337);
x_376 = lean_box(1);
x_377 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
lean_ctor_set_uint8(x_377, sizeof(void*)*2, x_372);
x_378 = lean_unsigned_to_nat(2u);
x_379 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_380, 0, x_374);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*2, x_372);
x_381 = lean_format_group(x_380);
x_382 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_382, 0, x_322);
lean_ctor_set(x_382, 1, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*2, x_372);
if (lean_is_scalar(x_336)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_336;
}
lean_ctor_set(x_383, 0, x_343);
lean_ctor_set(x_383, 1, x_382);
if (lean_is_scalar(x_323)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_323;
}
lean_ctor_set(x_384, 0, x_342);
lean_ctor_set(x_384, 1, x_383);
x_7 = x_13;
x_8 = x_384;
goto _start;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_337);
lean_dec(x_320);
if (lean_is_scalar(x_336)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_336;
}
lean_ctor_set(x_386, 0, x_343);
lean_ctor_set(x_386, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_323;
}
lean_ctor_set(x_387, 0, x_342);
lean_ctor_set(x_387, 1, x_386);
x_7 = x_13;
x_8 = x_387;
goto _start;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_337);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_326);
lean_ctor_set(x_389, 1, x_320);
if (lean_is_scalar(x_338)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_338;
}
lean_ctor_set(x_390, 0, x_335);
if (lean_is_scalar(x_336)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_336;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_323;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_391);
x_7 = x_13;
x_8 = x_392;
goto _start;
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_394 = lean_ctor_get(x_8, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_395 = x_8;
} else {
 lean_dec_ref(x_8);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_15, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_15, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_398 = x_15;
} else {
 lean_dec_ref(x_15);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_319, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_319, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_319, 4);
lean_inc(x_401);
lean_dec(x_319);
x_402 = lean_simp_macro_scopes(x_399);
x_403 = l_List_isEmpty___rarg(x_394);
lean_inc(x_2);
x_404 = l_Lean_MetavarContext_instantiateMVars(x_2, x_400);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec(x_404);
lean_inc(x_2);
x_406 = l_Lean_MetavarContext_instantiateMVars(x_2, x_401);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec(x_406);
x_408 = l_System_FilePath_dirName___closed__1;
x_409 = l_Lean_Name_toStringWithSep___main(x_408, x_402);
x_410 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_411 = 0;
x_412 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_413 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_412);
lean_ctor_set_uint8(x_413, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_414 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_405);
x_415 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*2, x_411);
x_416 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_417 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set_uint8(x_417, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_418 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_407);
x_419 = lean_box(1);
x_420 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*2, x_411);
x_421 = lean_unsigned_to_nat(2u);
x_422 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_420);
x_423 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_423, 0, x_417);
lean_ctor_set(x_423, 1, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*2, x_411);
x_424 = lean_format_group(x_423);
x_425 = lean_box(0);
x_426 = lean_box(0);
if (x_403 == 0)
{
uint8_t x_439; 
x_439 = l_Lean_Format_isNil(x_397);
if (x_439 == 0)
{
lean_object* x_440; 
x_440 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_440, 0, x_397);
lean_ctor_set(x_440, 1, x_419);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_411);
if (lean_obj_tag(x_394) == 0)
{
lean_dec(x_396);
x_427 = x_440;
goto block_438;
}
else
{
if (lean_obj_tag(x_396) == 0)
{
lean_dec(x_394);
x_427 = x_440;
goto block_438;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_441 = lean_ctor_get(x_396, 0);
lean_inc(x_441);
lean_dec(x_396);
x_442 = l_List_reverse___rarg(x_394);
x_443 = l_Lean_Format_flatten___main___closed__1;
x_444 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_442, x_443);
x_445 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_446 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set_uint8(x_446, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_447 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_441);
x_448 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_448, 0, x_419);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set_uint8(x_448, sizeof(void*)*2, x_411);
x_449 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_449, 0, x_421);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_450, 0, x_446);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*2, x_411);
x_451 = lean_format_group(x_450);
x_452 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_452, 0, x_440);
lean_ctor_set(x_452, 1, x_451);
lean_ctor_set_uint8(x_452, sizeof(void*)*2, x_411);
x_427 = x_452;
goto block_438;
}
}
}
else
{
if (lean_obj_tag(x_394) == 0)
{
lean_dec(x_396);
x_427 = x_397;
goto block_438;
}
else
{
if (lean_obj_tag(x_396) == 0)
{
lean_dec(x_394);
x_427 = x_397;
goto block_438;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_453 = lean_ctor_get(x_396, 0);
lean_inc(x_453);
lean_dec(x_396);
x_454 = l_List_reverse___rarg(x_394);
x_455 = l_Lean_Format_flatten___main___closed__1;
x_456 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_454, x_455);
x_457 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_458 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*2, x_411);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_459 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_453);
x_460 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_460, 0, x_419);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set_uint8(x_460, sizeof(void*)*2, x_411);
x_461 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_461, 0, x_421);
lean_ctor_set(x_461, 1, x_460);
x_462 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_462, 0, x_458);
lean_ctor_set(x_462, 1, x_461);
lean_ctor_set_uint8(x_462, sizeof(void*)*2, x_411);
x_463 = lean_format_group(x_462);
x_464 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_464, 0, x_397);
lean_ctor_set(x_464, 1, x_463);
lean_ctor_set_uint8(x_464, sizeof(void*)*2, x_411);
x_427 = x_464;
goto block_438;
}
}
}
}
else
{
lean_dec(x_396);
lean_dec(x_394);
x_427 = x_397;
goto block_438;
}
block_438:
{
uint8_t x_428; 
x_428 = l_Lean_Format_isNil(x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_419);
lean_ctor_set_uint8(x_429, sizeof(void*)*2, x_411);
x_430 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_424);
lean_ctor_set_uint8(x_430, sizeof(void*)*2, x_411);
if (lean_is_scalar(x_398)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_398;
}
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_430);
if (lean_is_scalar(x_395)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_395;
}
lean_ctor_set(x_432, 0, x_425);
lean_ctor_set(x_432, 1, x_431);
x_7 = x_13;
x_8 = x_432;
goto _start;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_434, 0, x_427);
lean_ctor_set(x_434, 1, x_424);
lean_ctor_set_uint8(x_434, sizeof(void*)*2, x_411);
if (lean_is_scalar(x_398)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_398;
}
lean_ctor_set(x_435, 0, x_426);
lean_ctor_set(x_435, 1, x_434);
if (lean_is_scalar(x_395)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_395;
}
lean_ctor_set(x_436, 0, x_425);
lean_ctor_set(x_436, 1, x_435);
x_7 = x_13;
x_8 = x_436;
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
