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
lean_object* l_Lean_IR_addDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__1;
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__2;
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__0;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_IR_addExtern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_IR_addExtern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec_ref(x_6);
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
lean_dec_ref(x_6);
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
lean_dec_ref(x_6);
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
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_IR_addExtern_spec__0(x_12, x_3, x_4, x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_43; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_2);
lean_inc_ref(x_22);
x_43 = l_Lean_IR_addDecl___redArg(x_22, x_4, x_21);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_IR_Decl_name(x_22);
x_46 = l_Lean_isPrivateName(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_st_ref_take(x_4, x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 5);
lean_dec(x_52);
x_53 = l_Lean_Compiler_LCNF_setDeclPublic(x_51, x_45);
x_54 = l_Lean_IR_addExtern___closed__3;
lean_ctor_set(x_48, 5, x_54);
lean_ctor_set(x_48, 0, x_53);
x_55 = lean_st_ref_set(x_4, x_48, x_49);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_23 = x_4;
x_24 = x_56;
goto block_42;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_ctor_get(x_48, 2);
x_60 = lean_ctor_get(x_48, 3);
x_61 = lean_ctor_get(x_48, 4);
x_62 = lean_ctor_get(x_48, 6);
x_63 = lean_ctor_get(x_48, 7);
x_64 = lean_ctor_get(x_48, 8);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_65 = l_Lean_Compiler_LCNF_setDeclPublic(x_57, x_45);
x_66 = l_Lean_IR_addExtern___closed__3;
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_61);
lean_ctor_set(x_67, 5, x_66);
lean_ctor_set(x_67, 6, x_62);
lean_ctor_set(x_67, 7, x_63);
lean_ctor_set(x_67, 8, x_64);
x_68 = lean_st_ref_set(x_4, x_67, x_49);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_23 = x_4;
x_24 = x_69;
goto block_42;
}
}
else
{
lean_dec(x_45);
x_23 = x_4;
x_24 = x_44;
goto block_42;
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_4);
return x_43;
}
block_42:
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_st_ref_get(x_23, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_29, x_22);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_23);
lean_dec_ref(x_22);
x_31 = lean_box(0);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_25);
x_32 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_22);
lean_dec_ref(x_22);
x_33 = l_Lean_IR_addDecl___redArg(x_32, x_23, x_28);
lean_dec(x_23);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_36);
lean_dec(x_34);
x_37 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_36, x_22);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
lean_dec_ref(x_22);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_22);
lean_dec_ref(x_22);
x_41 = l_Lean_IR_addDecl___redArg(x_40, x_23, x_35);
lean_dec(x_23);
return x_41;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_19);
if (x_70 == 0)
{
return x_19;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_19, 0);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_19);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_13);
if (x_74 == 0)
{
return x_13;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_13, 0);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_13);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_6);
if (x_78 == 0)
{
return x_6;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_6, 0);
x_80 = lean_ctor_get(x_6, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_6);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
