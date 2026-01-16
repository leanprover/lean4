// Lean compiler output
// Module: Lean.Meta.Tactic.CasesOnStuckLHS
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.SplitIf import Lean.ProjFns
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Meta_casesOnStuckLHS___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Meta_casesOnStuckLHS___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesOnStuckLHS___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Environment_getProjectionFnInfo_x3f(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 11)
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_1 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isConst(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_constName_x21(x_11);
x_18 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(x_17, x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Expr_getAppNumArgs(x_1);
x_22 = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_23, x_25);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec_ref(x_11);
x_28 = lean_st_ref_get(x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Lean_Environment_find_x3f(x_29, x_27, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_26);
lean_free_object(x_18);
x_7 = lean_box(0);
goto block_10;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
x_35 = lean_array_get_size(x_26);
x_36 = l_Lean_RecursorVal_getMajorIdx(x_34);
lean_dec_ref(x_34);
x_37 = lean_nat_dec_le(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_Lean_instInhabitedExpr;
x_39 = lean_array_get(x_38, x_26, x_36);
lean_dec(x_36);
lean_dec_ref(x_26);
x_40 = l_Lean_Expr_consumeMData(x_39);
lean_dec(x_39);
x_41 = l_Lean_Expr_isFVar(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_40);
lean_free_object(x_31);
x_42 = lean_box(0);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Expr_fvarId_x21(x_40);
lean_dec_ref(x_40);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
}
else
{
lean_object* x_44; 
lean_dec(x_36);
lean_free_object(x_31);
lean_dec_ref(x_26);
x_44 = lean_box(0);
lean_ctor_set(x_18, 0, x_44);
return x_18;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_dec_ref(x_26);
lean_free_object(x_18);
x_7 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_31, 0);
lean_inc(x_45);
lean_dec(x_31);
if (lean_obj_tag(x_45) == 7)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
lean_dec_ref(x_45);
x_47 = lean_array_get_size(x_26);
x_48 = l_Lean_RecursorVal_getMajorIdx(x_46);
lean_dec_ref(x_46);
x_49 = lean_nat_dec_le(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_instInhabitedExpr;
x_51 = lean_array_get(x_50, x_26, x_48);
lean_dec(x_48);
lean_dec_ref(x_26);
x_52 = l_Lean_Expr_consumeMData(x_51);
lean_dec(x_51);
x_53 = l_Lean_Expr_isFVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec_ref(x_52);
x_54 = lean_box(0);
lean_ctor_set(x_18, 0, x_54);
return x_18;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_52);
lean_dec_ref(x_52);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_18, 0, x_56);
return x_18;
}
}
else
{
lean_object* x_57; 
lean_dec(x_48);
lean_dec_ref(x_26);
x_57 = lean_box(0);
lean_ctor_set(x_18, 0, x_57);
return x_18;
}
}
else
{
lean_dec(x_45);
lean_dec_ref(x_26);
lean_free_object(x_18);
x_7 = lean_box(0);
goto block_10;
}
}
}
}
else
{
lean_dec_ref(x_26);
lean_free_object(x_18);
lean_dec_ref(x_11);
x_7 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_11);
x_58 = lean_ctor_get(x_20, 0);
lean_inc(x_58);
lean_dec_ref(x_20);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_array_get_size(x_26);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_59);
lean_dec_ref(x_26);
x_62 = lean_box(0);
lean_ctor_set(x_18, 0, x_62);
return x_18;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_free_object(x_18);
x_63 = l_Lean_instInhabitedExpr;
x_64 = lean_array_get(x_63, x_26, x_59);
lean_dec(x_59);
lean_dec_ref(x_26);
x_1 = x_64;
goto _start;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_18, 0);
lean_inc(x_66);
lean_dec(x_18);
x_67 = l_Lean_Expr_getAppNumArgs(x_1);
x_68 = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0;
lean_inc(x_67);
x_69 = lean_mk_array(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_67, x_70);
lean_dec(x_67);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_69, x_71);
if (lean_obj_tag(x_66) == 0)
{
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_11, 0);
lean_inc(x_73);
lean_dec_ref(x_11);
x_74 = lean_st_ref_get(x_5);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
lean_dec(x_74);
x_76 = 0;
x_77 = l_Lean_Environment_find_x3f(x_75, x_73, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_72);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_obj_tag(x_78) == 7)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_80);
lean_dec_ref(x_78);
x_81 = lean_array_get_size(x_72);
x_82 = l_Lean_RecursorVal_getMajorIdx(x_80);
lean_dec_ref(x_80);
x_83 = lean_nat_dec_le(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = l_Lean_instInhabitedExpr;
x_85 = lean_array_get(x_84, x_72, x_82);
lean_dec(x_82);
lean_dec_ref(x_72);
x_86 = l_Lean_Expr_consumeMData(x_85);
lean_dec(x_85);
x_87 = l_Lean_Expr_isFVar(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_86);
lean_dec(x_79);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Lean_Expr_fvarId_x21(x_86);
lean_dec_ref(x_86);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_79;
}
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec_ref(x_72);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
else
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec_ref(x_72);
x_7 = lean_box(0);
goto block_10;
}
}
}
else
{
lean_dec_ref(x_72);
lean_dec_ref(x_11);
x_7 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec_ref(x_11);
x_95 = lean_ctor_get(x_66, 0);
lean_inc(x_95);
lean_dec_ref(x_66);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_array_get_size(x_72);
x_98 = lean_nat_dec_lt(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec_ref(x_72);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lean_instInhabitedExpr;
x_102 = lean_array_get(x_101, x_72, x_96);
lean_dec(x_96);
lean_dec_ref(x_72);
x_1 = x_102;
goto _start;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_104 = !lean_is_exclusive(x_18);
if (x_104 == 0)
{
return x_18;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_18, 0);
lean_inc(x_105);
lean_dec(x_18);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_9, x_2, x_7);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_casesOnStuckLHS___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'casesOnStuckLHS' failed", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_casesOnStuckLHS___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_casesOnStuckLHS___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_casesOnStuckLHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_matchEqHEqLHS_x3f(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(x_20, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_Meta_casesOnStuckLHS___closed__2;
x_25 = 0;
x_26 = lean_box(0);
x_27 = l_Lean_MVarId_cases(x_1, x_23, x_24, x_25, x_26, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_array_size(x_29);
x_31 = 0;
x_32 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(x_30, x_31, x_29);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_array_size(x_33);
x_35 = 0;
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(x_34, x_35, x_33);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_1);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_14;
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_1);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_14;
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_casesOnStuckLHS___closed__1;
x_13 = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(x_12, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_casesOnStuckLHS(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_casesOnStuckLHS(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_15 = x_7;
} else {
 lean_dec_ref(x_7);
 x_15 = lean_box(0);
}
x_21 = l_Lean_Exception_isInterrupt(x_14);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_14);
x_22 = l_Lean_Exception_isRuntime(x_14);
x_16 = x_22;
goto block_20;
}
else
{
x_16 = x_21;
goto block_20;
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 1, 0);
} else {
 x_18 = x_15;
 lean_ctor_set_tag(x_18, 0);
}
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(1, 1, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_casesOnStuckLHS_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0);
l_Lean_Meta_casesOnStuckLHS___closed__0 = _init_l_Lean_Meta_casesOnStuckLHS___closed__0();
lean_mark_persistent(l_Lean_Meta_casesOnStuckLHS___closed__0);
l_Lean_Meta_casesOnStuckLHS___closed__1 = _init_l_Lean_Meta_casesOnStuckLHS___closed__1();
lean_mark_persistent(l_Lean_Meta_casesOnStuckLHS___closed__1);
l_Lean_Meta_casesOnStuckLHS___closed__2 = _init_l_Lean_Meta_casesOnStuckLHS___closed__2();
lean_mark_persistent(l_Lean_Meta_casesOnStuckLHS___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
