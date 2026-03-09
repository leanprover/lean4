// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.SearchM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4;
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
extern lean_object* l_Lean_instInhabitedFVarId_default;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
x_2 = l_Lean_instInhabitedFVarId_default;
x_3 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_1, x_11);
if (x_12 == 0)
{
return x_2;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_72; 
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_2, 7);
lean_dec(x_73);
x_74 = lean_ctor_get(x_2, 6);
lean_dec(x_74);
x_75 = lean_ctor_get(x_2, 5);
lean_dec(x_75);
x_76 = lean_ctor_get(x_2, 4);
lean_dec(x_76);
x_77 = lean_ctor_get(x_2, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_2, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_2, 0);
lean_dec(x_80);
x_13 = x_2;
x_14 = x_72;
goto block_71;
}
else
{
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_70; 
x_15 = lean_array_fget(x_3, x_1);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 2);
x_19 = lean_ctor_get(x_15, 3);
x_20 = lean_ctor_get(x_15, 4);
x_21 = lean_ctor_get(x_15, 5);
x_22 = lean_ctor_get(x_15, 6);
x_23 = lean_ctor_get(x_15, 7);
x_24 = lean_ctor_get(x_15, 8);
x_25 = lean_ctor_get(x_15, 9);
x_26 = lean_ctor_get(x_15, 10);
x_27 = lean_ctor_get(x_15, 11);
x_28 = lean_ctor_get(x_15, 12);
x_29 = lean_ctor_get(x_15, 13);
x_30 = lean_ctor_get(x_15, 14);
x_31 = lean_ctor_get(x_15, 15);
x_32 = lean_ctor_get(x_15, 16);
x_33 = lean_ctor_get(x_15, 17);
x_34 = lean_ctor_get(x_15, 18);
x_35 = lean_ctor_get(x_15, 19);
x_36 = lean_ctor_get(x_15, 20);
x_37 = lean_ctor_get(x_15, 21);
x_38 = lean_ctor_get(x_15, 22);
x_39 = lean_ctor_get(x_15, 23);
x_40 = lean_ctor_get(x_15, 24);
x_41 = lean_ctor_get(x_15, 25);
x_42 = lean_ctor_get(x_15, 26);
x_43 = lean_ctor_get(x_15, 27);
x_44 = lean_ctor_get(x_15, 28);
x_45 = lean_ctor_get(x_15, 29);
x_46 = lean_ctor_get(x_15, 30);
x_47 = lean_ctor_get(x_15, 31);
x_48 = lean_ctor_get(x_15, 32);
x_49 = lean_ctor_get(x_15, 33);
x_50 = lean_ctor_get(x_15, 34);
x_51 = lean_ctor_get(x_15, 35);
x_52 = lean_ctor_get(x_15, 36);
x_53 = lean_ctor_get(x_15, 37);
x_54 = lean_ctor_get(x_15, 38);
x_55 = lean_ctor_get(x_15, 39);
x_56 = lean_ctor_get(x_15, 40);
x_57 = lean_ctor_get(x_15, 41);
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
x_58 = x_15;
x_59 = x_70;
goto block_69;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_15);
x_58 = lean_box(0);
x_59 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_box(0);
x_61 = lean_array_fset(x_3, x_1, x_60);
if (x_59 == 0)
{
x_62 = x_58;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_68, 0, x_16);
lean_ctor_set(x_68, 1, x_17);
lean_ctor_set(x_68, 2, x_18);
lean_ctor_set(x_68, 3, x_19);
lean_ctor_set(x_68, 4, x_20);
lean_ctor_set(x_68, 5, x_21);
lean_ctor_set(x_68, 6, x_22);
lean_ctor_set(x_68, 7, x_23);
lean_ctor_set(x_68, 8, x_24);
lean_ctor_set(x_68, 9, x_25);
lean_ctor_set(x_68, 10, x_26);
lean_ctor_set(x_68, 11, x_27);
lean_ctor_set(x_68, 12, x_28);
lean_ctor_set(x_68, 13, x_29);
lean_ctor_set(x_68, 14, x_30);
lean_ctor_set(x_68, 15, x_31);
lean_ctor_set(x_68, 16, x_32);
lean_ctor_set(x_68, 17, x_33);
lean_ctor_set(x_68, 18, x_34);
lean_ctor_set(x_68, 19, x_35);
lean_ctor_set(x_68, 20, x_36);
lean_ctor_set(x_68, 21, x_37);
lean_ctor_set(x_68, 22, x_38);
lean_ctor_set(x_68, 23, x_39);
lean_ctor_set(x_68, 24, x_40);
lean_ctor_set(x_68, 25, x_41);
lean_ctor_set(x_68, 26, x_42);
lean_ctor_set(x_68, 27, x_43);
lean_ctor_set(x_68, 28, x_44);
lean_ctor_set(x_68, 29, x_45);
lean_ctor_set(x_68, 30, x_46);
lean_ctor_set(x_68, 31, x_47);
lean_ctor_set(x_68, 32, x_48);
lean_ctor_set(x_68, 33, x_49);
lean_ctor_set(x_68, 34, x_50);
lean_ctor_set(x_68, 35, x_51);
lean_ctor_set(x_68, 36, x_52);
lean_ctor_set(x_68, 37, x_53);
lean_ctor_set(x_68, 38, x_54);
lean_ctor_set(x_68, 39, x_55);
lean_ctor_set(x_68, 40, x_56);
lean_ctor_set(x_68, 41, x_57);
x_62 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_63; lean_object* x_64; 
lean_ctor_set_uint8(x_62, sizeof(void*)*42, x_12);
x_63 = lean_array_fset(x_61, x_1, x_62);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_63);
x_64 = x_13;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_4);
lean_ctor_set(x_66, 2, x_5);
lean_ctor_set(x_66, 3, x_6);
lean_ctor_set(x_66, 4, x_7);
lean_ctor_set(x_66, 5, x_8);
lean_ctor_set(x_66, 6, x_9);
lean_ctor_set(x_66, 7, x_10);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_7 = x_4;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_9 = lean_st_ref_take(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_ctor_get(x_9, 6);
x_16 = lean_ctor_get(x_9, 7);
x_17 = lean_ctor_get(x_9, 8);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 2);
lean_dec(x_33);
x_18 = x_9;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_num___override(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_22);
x_23 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_22);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_23);
x_24 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 4, x_13);
lean_ctor_set(x_28, 5, x_14);
lean_ctor_set(x_28, 6, x_15);
lean_ctor_set(x_28, 7, x_16);
lean_ctor_set(x_28, 8, x_17);
x_24 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_14 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(x_12);
x_15 = lean_ctor_get(x_14, 0);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
x_16 = x_14;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_51; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_st_ref_take(x_2);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
x_22 = x_19;
x_23 = x_51;
goto block_50;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_16);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_18);
x_25 = l_Lean_PersistentArray_push___redArg(x_20, x_24);
lean_inc(x_16);
x_26 = l_Lean_FVarIdSet_insert(x_21, x_16);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_25);
x_27 = x_22;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_26);
x_27 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_st_ref_set(x_2, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_3);
x_30 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_31 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_30, x_29, x_4);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_31, 0);
lean_dec(x_39);
x_32 = x_31;
x_33 = x_38;
goto block_37;
}
else
{
lean_dec(x_31);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_16);
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_16);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_16);
x_40 = lean_ctor_get(x_31, 0);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
x_41 = x_31;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_17, 0);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
x_53 = x_17;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_17);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_mkCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
}
#ifdef __cplusplus
}
#endif
