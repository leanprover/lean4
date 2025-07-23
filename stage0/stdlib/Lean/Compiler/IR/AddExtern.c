// Lean compiler output
// Module: Lean.Compiler.IR.AddExtern
// Imports: Lean.CoreM Lean.Compiler.BorrowedAnnotation Lean.Compiler.ExternAttr Lean.Compiler.IR.Basic Lean.Compiler.IR.Boxing Lean.Compiler.IR.CompilerM Lean.Compiler.IR.ToIRType Lean.Compiler.LCNF.MonoTypes
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
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__1;
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
LEAN_EXPORT lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__2;
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__0;
lean_object* l_Lean_IR_addDeclAux(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_IR_addExtern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_IR_addExtern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 7)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_14);
lean_dec(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_13);
x_15 = l_Lean_IR_toIRType(x_13, x_2, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_isMarkedBorrowed(x_13);
lean_dec_ref(x_13);
lean_inc(x_8);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_array_push(x_11, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_8, x_21);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_20);
lean_ctor_set(x_1, 0, x_22);
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_free_object(x_5);
lean_dec(x_11);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_30);
lean_dec(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_29);
x_31 = l_Lean_IR_toIRType(x_29, x_2, x_3, x_4);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Lean_isMarkedBorrowed(x_29);
lean_dec_ref(x_29);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_34);
x_36 = lean_array_push(x_28, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_8, x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_38);
x_4 = x_33;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_43 = x_31;
} else {
 lean_dec_ref(x_31);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_47 = x_5;
} else {
 lean_dec_ref(x_5);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_49);
lean_dec(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_48);
x_50 = l_Lean_IR_toIRType(x_48, x_2, x_3, x_4);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_isMarkedBorrowed(x_48);
lean_dec_ref(x_48);
lean_inc(x_45);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_53);
x_55 = lean_array_push(x_46, x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_45, x_56);
lean_dec(x_45);
if (lean_is_scalar(x_47)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_47;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_49);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_1 = x_59;
x_4 = x_52;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_1, 1);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_5);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_5, 1);
lean_dec(x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_4);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
lean_dec(x_5);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
lean_ctor_set(x_1, 1, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_4);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_75 = x_5;
} else {
 lean_dec_ref(x_5);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_6);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_4);
return x_78;
}
}
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addExtern___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addExtern___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_add_extern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_getOtherDeclMonoType(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_IR_addExtern___closed__0;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_Loop_forIn_loop___at___Lean_IR_addExtern_spec__0(x_12, x_3, x_4, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_4);
x_19 = l_Lean_IR_toIRType(x_18, x_3, x_4, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_ref_take(x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 5);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_2);
lean_inc_ref(x_28);
x_29 = l_Lean_IR_addDeclAux(x_26, x_28);
x_30 = l_Lean_IR_addExtern___closed__3;
lean_ctor_set(x_23, 5, x_30);
lean_ctor_set(x_23, 0, x_29);
x_31 = lean_st_ref_set(x_4, x_23, x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_st_ref_get(x_4, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_37);
lean_dec(x_35);
lean_inc_ref(x_28);
x_38 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_37, x_28);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_28);
lean_dec(x_4);
x_39 = lean_box(0);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_33);
x_40 = lean_st_ref_take(x_4, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 5);
lean_dec(x_45);
x_46 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_28);
x_47 = l_Lean_IR_addDeclAux(x_44, x_46);
lean_ctor_set(x_41, 5, x_30);
lean_ctor_set(x_41, 0, x_47);
x_48 = lean_st_ref_set(x_4, x_41, x_42);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
x_59 = lean_ctor_get(x_41, 4);
x_60 = lean_ctor_get(x_41, 6);
x_61 = lean_ctor_get(x_41, 7);
x_62 = lean_ctor_get(x_41, 8);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_63 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_28);
x_64 = l_Lean_IR_addDeclAux(x_55, x_63);
x_65 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_56);
lean_ctor_set(x_65, 2, x_57);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_59);
lean_ctor_set(x_65, 5, x_30);
lean_ctor_set(x_65, 6, x_60);
lean_ctor_set(x_65, 7, x_61);
lean_ctor_set(x_65, 8, x_62);
x_66 = lean_st_ref_set(x_4, x_65, x_42);
lean_dec(x_4);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_33, 0);
x_72 = lean_ctor_get(x_33, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_33);
x_73 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_73);
lean_dec(x_71);
lean_inc_ref(x_28);
x_74 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_73, x_28);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_28);
lean_dec(x_4);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_77 = lean_st_ref_take(x_4, x_72);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 2);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_78, 3);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_78, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_78, 8);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 x_88 = x_78;
} else {
 lean_dec_ref(x_78);
 x_88 = lean_box(0);
}
x_89 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_28);
x_90 = l_Lean_IR_addDeclAux(x_80, x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 9, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_82);
lean_ctor_set(x_91, 3, x_83);
lean_ctor_set(x_91, 4, x_84);
lean_ctor_set(x_91, 5, x_30);
lean_ctor_set(x_91, 6, x_85);
lean_ctor_set(x_91, 7, x_86);
lean_ctor_set(x_91, 8, x_87);
x_92 = lean_st_ref_set(x_4, x_91, x_79);
lean_dec(x_4);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
x_99 = lean_ctor_get(x_23, 2);
x_100 = lean_ctor_get(x_23, 3);
x_101 = lean_ctor_get(x_23, 4);
x_102 = lean_ctor_get(x_23, 6);
x_103 = lean_ctor_get(x_23, 7);
x_104 = lean_ctor_get(x_23, 8);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_105 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_17);
lean_ctor_set(x_105, 2, x_20);
lean_ctor_set(x_105, 3, x_2);
lean_inc_ref(x_105);
x_106 = l_Lean_IR_addDeclAux(x_97, x_105);
x_107 = l_Lean_IR_addExtern___closed__3;
x_108 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 5, x_107);
lean_ctor_set(x_108, 6, x_102);
lean_ctor_set(x_108, 7, x_103);
lean_ctor_set(x_108, 8, x_104);
x_109 = lean_st_ref_set(x_4, x_108, x_24);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = lean_st_ref_get(x_4, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_115);
lean_dec(x_112);
lean_inc_ref(x_105);
x_116 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_115, x_105);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_105);
lean_dec(x_4);
x_117 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_114);
x_119 = lean_st_ref_take(x_4, x_113);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 2);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_120, 3);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_120, 4);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_120, 6);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_120, 7);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_120, 8);
lean_inc_ref(x_129);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 lean_ctor_release(x_120, 6);
 lean_ctor_release(x_120, 7);
 lean_ctor_release(x_120, 8);
 x_130 = x_120;
} else {
 lean_dec_ref(x_120);
 x_130 = lean_box(0);
}
x_131 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_105);
x_132 = l_Lean_IR_addDeclAux(x_122, x_131);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 9, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_123);
lean_ctor_set(x_133, 2, x_124);
lean_ctor_set(x_133, 3, x_125);
lean_ctor_set(x_133, 4, x_126);
lean_ctor_set(x_133, 5, x_107);
lean_ctor_set(x_133, 6, x_127);
lean_ctor_set(x_133, 7, x_128);
lean_ctor_set(x_133, 8, x_129);
x_134 = lean_st_ref_set(x_4, x_133, x_121);
lean_dec(x_4);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_19);
if (x_139 == 0)
{
return x_19;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_19, 0);
x_141 = lean_ctor_get(x_19, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_19);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_13);
if (x_143 == 0)
{
return x_13;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_13, 0);
x_145 = lean_ctor_get(x_13, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_13);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_6);
if (x_147 == 0)
{
return x_6;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_6, 0);
x_149 = lean_ctor_get(x_6, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_6);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_addExtern___closed__0 = _init_l_Lean_IR_addExtern___closed__0();
lean_mark_persistent(l_Lean_IR_addExtern___closed__0);
l_Lean_IR_addExtern___closed__1 = _init_l_Lean_IR_addExtern___closed__1();
lean_mark_persistent(l_Lean_IR_addExtern___closed__1);
l_Lean_IR_addExtern___closed__2 = _init_l_Lean_IR_addExtern___closed__2();
lean_mark_persistent(l_Lean_IR_addExtern___closed__2);
l_Lean_IR_addExtern___closed__3 = _init_l_Lean_IR_addExtern___closed__3();
lean_mark_persistent(l_Lean_IR_addExtern___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
