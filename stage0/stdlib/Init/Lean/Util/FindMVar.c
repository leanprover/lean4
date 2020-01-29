// Lean compiler output
// Module: Init.Lean.Util.FindMVar
// Imports: Init.Lean.Expr
#include "runtime/lean.h"
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
lean_object* l_Lean_FindMVar_visit(lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
extern uint8_t l_String_posOfAux___main___closed__2;
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_Expr_findMVar_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_String_posOfAux___main___closed__2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
else
{
uint8_t x_7; 
x_7 = l_String_posOfAux___main___closed__1;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_2(x_1, x_2, x_3);
return x_8;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
else
{
uint8_t x_9; 
x_9 = l_String_posOfAux___main___closed__2;
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_apply_2(x_1, x_2, x_3);
return x_10;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_FindMVar_main___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_String_posOfAux___main___closed__1;
if (x_10 == 0)
{
lean_dec(x_9);
return x_3;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
}
}
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasMVar(x_14);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_String_posOfAux___main___closed__2;
if (x_24 == 0)
{
lean_object* x_25; 
lean_inc(x_1);
x_25 = l_Lean_FindMVar_main___main(x_1, x_14, x_3);
if (lean_obj_tag(x_25) == 0)
{
x_16 = x_25;
goto block_22;
}
else
{
x_2 = x_15;
x_3 = x_25;
goto _start;
}
}
else
{
lean_dec(x_14);
x_16 = x_3;
goto block_22;
}
}
else
{
uint8_t x_27; 
x_27 = l_String_posOfAux___main___closed__1;
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_1);
x_28 = l_Lean_FindMVar_main___main(x_1, x_14, x_3);
if (lean_obj_tag(x_28) == 0)
{
x_16 = x_28;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = l_String_posOfAux___main___closed__2;
if (x_29 == 0)
{
x_2 = x_15;
x_3 = x_28;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_1);
return x_28;
}
}
}
else
{
lean_dec(x_14);
x_16 = x_3;
goto block_22;
}
}
}
else
{
uint8_t x_31; 
x_31 = l_String_posOfAux___main___closed__2;
if (x_31 == 0)
{
lean_object* x_32; 
lean_inc(x_1);
x_32 = l_Lean_FindMVar_main___main(x_1, x_14, x_3);
if (lean_obj_tag(x_32) == 0)
{
x_16 = x_32;
goto block_22;
}
else
{
x_2 = x_15;
x_3 = x_32;
goto _start;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_3;
}
}
block_22:
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_String_posOfAux___main___closed__2;
if (x_18 == 0)
{
x_2 = x_15;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_1);
return x_16;
}
}
else
{
uint8_t x_20; 
x_20 = l_String_posOfAux___main___closed__1;
if (x_20 == 0)
{
x_2 = x_15;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_1);
return x_16;
}
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_34);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_String_posOfAux___main___closed__2;
if (x_44 == 0)
{
lean_object* x_45; 
lean_inc(x_1);
x_45 = l_Lean_FindMVar_main___main(x_1, x_34, x_3);
if (lean_obj_tag(x_45) == 0)
{
x_36 = x_45;
goto block_42;
}
else
{
x_2 = x_35;
x_3 = x_45;
goto _start;
}
}
else
{
lean_dec(x_34);
x_36 = x_3;
goto block_42;
}
}
else
{
uint8_t x_47; 
x_47 = l_String_posOfAux___main___closed__1;
if (x_47 == 0)
{
lean_object* x_48; 
lean_inc(x_1);
x_48 = l_Lean_FindMVar_main___main(x_1, x_34, x_3);
if (lean_obj_tag(x_48) == 0)
{
x_36 = x_48;
goto block_42;
}
else
{
uint8_t x_49; 
x_49 = l_String_posOfAux___main___closed__2;
if (x_49 == 0)
{
x_2 = x_35;
x_3 = x_48;
goto _start;
}
else
{
lean_dec(x_35);
lean_dec(x_1);
return x_48;
}
}
}
else
{
lean_dec(x_34);
x_36 = x_3;
goto block_42;
}
}
}
else
{
uint8_t x_51; 
x_51 = l_String_posOfAux___main___closed__2;
if (x_51 == 0)
{
lean_object* x_52; 
lean_inc(x_1);
x_52 = l_Lean_FindMVar_main___main(x_1, x_34, x_3);
if (lean_obj_tag(x_52) == 0)
{
x_36 = x_52;
goto block_42;
}
else
{
x_2 = x_35;
x_3 = x_52;
goto _start;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
return x_3;
}
}
block_42:
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_String_posOfAux___main___closed__2;
if (x_38 == 0)
{
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_dec(x_35);
lean_dec(x_1);
return x_36;
}
}
else
{
uint8_t x_40; 
x_40 = l_String_posOfAux___main___closed__1;
if (x_40 == 0)
{
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_dec(x_35);
lean_dec(x_1);
return x_36;
}
}
}
}
case 7:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Expr_hasMVar(x_54);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_String_posOfAux___main___closed__2;
if (x_64 == 0)
{
lean_object* x_65; 
lean_inc(x_1);
x_65 = l_Lean_FindMVar_main___main(x_1, x_54, x_3);
if (lean_obj_tag(x_65) == 0)
{
x_56 = x_65;
goto block_62;
}
else
{
x_2 = x_55;
x_3 = x_65;
goto _start;
}
}
else
{
lean_dec(x_54);
x_56 = x_3;
goto block_62;
}
}
else
{
uint8_t x_67; 
x_67 = l_String_posOfAux___main___closed__1;
if (x_67 == 0)
{
lean_object* x_68; 
lean_inc(x_1);
x_68 = l_Lean_FindMVar_main___main(x_1, x_54, x_3);
if (lean_obj_tag(x_68) == 0)
{
x_56 = x_68;
goto block_62;
}
else
{
uint8_t x_69; 
x_69 = l_String_posOfAux___main___closed__2;
if (x_69 == 0)
{
x_2 = x_55;
x_3 = x_68;
goto _start;
}
else
{
lean_dec(x_55);
lean_dec(x_1);
return x_68;
}
}
}
else
{
lean_dec(x_54);
x_56 = x_3;
goto block_62;
}
}
}
else
{
uint8_t x_71; 
x_71 = l_String_posOfAux___main___closed__2;
if (x_71 == 0)
{
lean_object* x_72; 
lean_inc(x_1);
x_72 = l_Lean_FindMVar_main___main(x_1, x_54, x_3);
if (lean_obj_tag(x_72) == 0)
{
x_56 = x_72;
goto block_62;
}
else
{
x_2 = x_55;
x_3 = x_72;
goto _start;
}
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_3;
}
}
block_62:
{
uint8_t x_57; 
x_57 = l_Lean_Expr_hasMVar(x_55);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_String_posOfAux___main___closed__2;
if (x_58 == 0)
{
x_2 = x_55;
x_3 = x_56;
goto _start;
}
else
{
lean_dec(x_55);
lean_dec(x_1);
return x_56;
}
}
else
{
uint8_t x_60; 
x_60 = l_String_posOfAux___main___closed__1;
if (x_60 == 0)
{
x_2 = x_55;
x_3 = x_56;
goto _start;
}
else
{
lean_dec(x_55);
lean_dec(x_1);
return x_56;
}
}
}
}
case 8:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_84; lean_object* x_96; 
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 3);
lean_inc(x_76);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Expr_hasMVar(x_74);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = l_String_posOfAux___main___closed__2;
if (x_102 == 0)
{
lean_object* x_103; 
lean_inc(x_1);
x_103 = l_Lean_FindMVar_main___main(x_1, x_74, x_3);
if (lean_obj_tag(x_103) == 0)
{
x_84 = x_103;
goto block_95;
}
else
{
x_96 = x_103;
goto block_100;
}
}
else
{
lean_dec(x_74);
x_84 = x_3;
goto block_95;
}
}
else
{
uint8_t x_104; 
x_104 = l_String_posOfAux___main___closed__1;
if (x_104 == 0)
{
lean_object* x_105; 
lean_inc(x_1);
x_105 = l_Lean_FindMVar_main___main(x_1, x_74, x_3);
if (lean_obj_tag(x_105) == 0)
{
x_84 = x_105;
goto block_95;
}
else
{
x_96 = x_105;
goto block_100;
}
}
else
{
lean_dec(x_74);
x_84 = x_3;
goto block_95;
}
}
}
else
{
uint8_t x_106; 
x_106 = l_String_posOfAux___main___closed__2;
if (x_106 == 0)
{
lean_object* x_107; 
lean_inc(x_1);
x_107 = l_Lean_FindMVar_main___main(x_1, x_74, x_3);
if (lean_obj_tag(x_107) == 0)
{
x_84 = x_107;
goto block_95;
}
else
{
x_96 = x_107;
goto block_100;
}
}
else
{
lean_dec(x_74);
x_96 = x_3;
goto block_100;
}
}
block_83:
{
uint8_t x_78; 
x_78 = l_Lean_Expr_hasMVar(x_76);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_String_posOfAux___main___closed__2;
if (x_79 == 0)
{
x_2 = x_76;
x_3 = x_77;
goto _start;
}
else
{
lean_dec(x_76);
lean_dec(x_1);
return x_77;
}
}
else
{
uint8_t x_81; 
x_81 = l_String_posOfAux___main___closed__1;
if (x_81 == 0)
{
x_2 = x_76;
x_3 = x_77;
goto _start;
}
else
{
lean_dec(x_76);
lean_dec(x_1);
return x_77;
}
}
}
block_95:
{
uint8_t x_85; 
x_85 = l_Lean_Expr_hasMVar(x_75);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_String_posOfAux___main___closed__2;
if (x_86 == 0)
{
lean_object* x_87; 
lean_inc(x_1);
x_87 = l_Lean_FindMVar_main___main(x_1, x_75, x_84);
if (lean_obj_tag(x_87) == 0)
{
x_77 = x_87;
goto block_83;
}
else
{
x_2 = x_76;
x_3 = x_87;
goto _start;
}
}
else
{
lean_dec(x_75);
if (lean_obj_tag(x_84) == 0)
{
x_77 = x_84;
goto block_83;
}
else
{
lean_dec(x_76);
lean_dec(x_1);
return x_84;
}
}
}
else
{
uint8_t x_89; 
x_89 = l_String_posOfAux___main___closed__1;
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc(x_1);
x_90 = l_Lean_FindMVar_main___main(x_1, x_75, x_84);
if (lean_obj_tag(x_90) == 0)
{
x_77 = x_90;
goto block_83;
}
else
{
uint8_t x_91; 
x_91 = l_String_posOfAux___main___closed__2;
if (x_91 == 0)
{
x_2 = x_76;
x_3 = x_90;
goto _start;
}
else
{
lean_dec(x_76);
lean_dec(x_1);
return x_90;
}
}
}
else
{
lean_dec(x_75);
if (lean_obj_tag(x_84) == 0)
{
x_77 = x_84;
goto block_83;
}
else
{
uint8_t x_93; 
x_93 = l_String_posOfAux___main___closed__2;
if (x_93 == 0)
{
x_2 = x_76;
x_3 = x_84;
goto _start;
}
else
{
lean_dec(x_76);
lean_dec(x_1);
return x_84;
}
}
}
}
}
block_100:
{
uint8_t x_97; 
x_97 = l_String_posOfAux___main___closed__2;
if (x_97 == 0)
{
lean_object* x_98; 
lean_inc(x_1);
x_98 = l_Lean_FindMVar_main___main(x_1, x_75, x_96);
if (lean_obj_tag(x_98) == 0)
{
x_77 = x_98;
goto block_83;
}
else
{
x_2 = x_76;
x_3 = x_98;
goto _start;
}
}
else
{
lean_dec(x_75);
if (lean_obj_tag(x_96) == 0)
{
x_77 = x_96;
goto block_83;
}
else
{
lean_dec(x_76);
lean_dec(x_1);
return x_96;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
lean_dec(x_2);
x_109 = l_Lean_Expr_hasMVar(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_String_posOfAux___main___closed__2;
if (x_110 == 0)
{
x_2 = x_108;
goto _start;
}
else
{
lean_dec(x_108);
lean_dec(x_1);
return x_3;
}
}
else
{
uint8_t x_112; 
x_112 = l_String_posOfAux___main___closed__1;
if (x_112 == 0)
{
x_2 = x_108;
goto _start;
}
else
{
lean_dec(x_108);
lean_dec(x_1);
return x_3;
}
}
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_dec(x_2);
x_115 = l_String_posOfAux___main___closed__2;
if (x_115 == 0)
{
x_2 = x_114;
goto _start;
}
else
{
lean_dec(x_114);
lean_dec(x_1);
return x_3;
}
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_2, 2);
lean_inc(x_117);
lean_dec(x_2);
x_118 = l_Lean_Expr_hasMVar(x_117);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_String_posOfAux___main___closed__2;
if (x_119 == 0)
{
x_2 = x_117;
goto _start;
}
else
{
lean_dec(x_117);
lean_dec(x_1);
return x_3;
}
}
else
{
uint8_t x_121; 
x_121 = l_String_posOfAux___main___closed__1;
if (x_121 == 0)
{
x_2 = x_117;
goto _start;
}
else
{
lean_dec(x_117);
lean_dec(x_1);
return x_3;
}
}
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_2, 2);
lean_inc(x_123);
lean_dec(x_2);
x_124 = l_String_posOfAux___main___closed__2;
if (x_124 == 0)
{
x_2 = x_123;
goto _start;
}
else
{
lean_dec(x_123);
lean_dec(x_1);
return x_3;
}
}
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_FindMVar_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_findMVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main(x_2, x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_FindMVar(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
