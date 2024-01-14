// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceJpArity
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.PassManager
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
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__8;
static lean_object* l_Lean_Compiler_LCNF_reduceJpArity___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__12;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__17;
static lean_object* l_Lean_Compiler_LCNF_reduceJpArity___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887_(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__14;
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__19;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__16;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__15;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__10;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__13;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceJpArity___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__9;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_19, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_22 = l_Lean_Compiler_LCNF_eraseParam(x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_array_push(x_16, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = 1;
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
x_5 = x_27;
x_11 = x_23;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_14, 2);
lean_inc(x_31);
x_32 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_31, x_19);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_array_push(x_18, x_14);
lean_ctor_set(x_15, 1, x_32);
lean_ctor_set(x_15, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_15);
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_4 = x_39;
x_5 = x_37;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_42, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_45 = l_Lean_Compiler_LCNF_eraseParam(x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_array_push(x_16, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_42);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_4, x_52);
x_4 = x_53;
x_5 = x_51;
x_11 = x_46;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; 
lean_dec(x_44);
x_55 = lean_ctor_get(x_14, 2);
lean_inc(x_55);
x_56 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_55, x_42);
x_57 = 1;
x_58 = lean_box(x_57);
x_59 = lean_array_push(x_16, x_58);
x_60 = lean_array_push(x_41, x_14);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = 1;
x_64 = lean_usize_add(x_4, x_63);
x_4 = x_64;
x_5 = x_62;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_18, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_21 = l_Lean_Compiler_LCNF_eraseParam(x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_array_push(x_15, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_4 = x_26;
x_10 = x_22;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec(x_20);
x_30 = lean_ctor_get(x_13, 2);
lean_inc(x_30);
x_31 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_30, x_18);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_array_push(x_15, x_33);
x_35 = lean_array_push(x_17, x_13);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_14, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_14);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_4 = x_36;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_42);
x_43 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_41, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_44 = l_Lean_Compiler_LCNF_eraseParam(x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_array_push(x_15, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_41);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_3, x_51);
x_3 = x_52;
x_4 = x_50;
x_10 = x_45;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; 
lean_dec(x_43);
x_54 = lean_ctor_get(x_13, 2);
lean_inc(x_54);
x_55 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_54, x_41);
x_56 = 1;
x_57 = lean_box(x_56);
x_58 = lean_array_push(x_15, x_57);
x_59 = lean_array_push(x_40, x_13);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = 1;
x_63 = lean_usize_add(x_3, x_62);
x_3 = x_63;
x_4 = x_61;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_16, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_array_fget(x_18, x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_19, x_28);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_29);
if (x_14 == 0)
{
size_t x_30; size_t x_31; 
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; 
x_33 = lean_array_push(x_17, x_27);
lean_ctor_set(x_4, 1, x_33);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_16);
x_37 = lean_array_fget(x_18, x_19);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_19, x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_20);
if (x_14 == 0)
{
size_t x_41; size_t x_42; 
lean_dec(x_37);
lean_ctor_set(x_4, 0, x_40);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; 
x_44 = lean_array_push(x_17, x_37);
lean_ctor_set(x_4, 1, x_44);
lean_ctor_set(x_4, 0, x_40);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
goto _start;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 2);
lean_inc(x_52);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
x_57 = lean_array_fget(x_50, x_51);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_51, x_58);
lean_dec(x_51);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 3, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_52);
if (x_14 == 0)
{
lean_object* x_61; size_t x_62; size_t x_63; 
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
x_62 = 1;
x_63 = lean_usize_add(x_3, x_62);
x_3 = x_63;
x_4 = x_61;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
x_65 = lean_array_push(x_49, x_57);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
x_67 = 1;
x_68 = lean_usize_add(x_3, x_67);
x_3 = x_68;
x_4 = x_66;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__6(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_9 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_14 = lean_ptr_addr(x_12);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
size_t x_20; uint8_t x_21; 
x_20 = lean_ptr_addr(x_8);
x_21 = lean_usize_dec_eq(x_20, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_29 = lean_ptr_addr(x_26);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_31 = x_1;
} else {
 lean_dec_ref(x_1);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
size_t x_34; uint8_t x_35; 
x_34 = lean_ptr_addr(x_8);
x_35 = lean_usize_dec_eq(x_34, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_36 = x_1;
} else {
 lean_dec_ref(x_1);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 4);
lean_inc(x_46);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_46, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 2);
lean_inc(x_51);
lean_inc(x_44);
x_52 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_44, x_50, x_51, x_48, x_3, x_4, x_5, x_6, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_45);
x_55 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_45, x_2, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; size_t x_58; size_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_59 = lean_ptr_addr(x_57);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_44);
x_61 = !lean_is_exclusive(x_1);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_1, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_1, 0);
lean_dec(x_63);
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_1, 0, x_53);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
else
{
lean_object* x_64; 
lean_dec(x_1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_55, 0, x_64);
return x_55;
}
}
else
{
size_t x_65; size_t x_66; uint8_t x_67; 
x_65 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_66 = lean_ptr_addr(x_53);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_1, 0);
lean_dec(x_70);
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_1, 0, x_53);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
else
{
lean_object* x_71; 
lean_dec(x_1);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_53);
lean_ctor_set(x_71, 1, x_57);
lean_ctor_set(x_55, 0, x_71);
return x_55;
}
}
else
{
lean_dec(x_57);
lean_dec(x_53);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_55, 0);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_55);
x_74 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_75 = lean_ptr_addr(x_72);
x_76 = lean_usize_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_44);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_77 = x_1;
} else {
 lean_dec_ref(x_1);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_53);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
else
{
size_t x_80; size_t x_81; uint8_t x_82; 
x_80 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_81 = lean_ptr_addr(x_53);
x_82 = lean_usize_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_83 = x_1;
} else {
 lean_dec_ref(x_1);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_72);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_73);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_72);
lean_dec(x_53);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_73);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_53);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_55);
if (x_87 == 0)
{
return x_55;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_55, 0);
x_89 = lean_ctor_get(x_55, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_55);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_47);
if (x_91 == 0)
{
return x_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_47, 0);
x_93 = lean_ctor_get(x_47, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_47);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 2:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 4);
lean_inc(x_97);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_98 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_97, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_box(0);
lean_inc(x_99);
x_102 = l_Lean_Compiler_LCNF_Code_collectUsed(x_99, x_101);
x_103 = lean_ctor_get(x_95, 2);
lean_inc(x_103);
lean_inc(x_103);
x_104 = l_Array_reverse___rarg(x_103);
x_105 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_get_size(x_104);
x_109 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_110 = 0;
x_111 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__2(x_104, x_109, x_110, x_107, x_2, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_104);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
lean_dec(x_113);
x_117 = l_Array_reverse___rarg(x_115);
x_118 = l_Array_reverse___rarg(x_116);
x_119 = lean_array_get_size(x_118);
x_120 = lean_array_get_size(x_103);
x_121 = lean_nat_dec_eq(x_119, x_120);
lean_dec(x_120);
lean_dec(x_119);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_103);
x_122 = !lean_is_exclusive(x_1);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_1, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_1, 0);
lean_dec(x_124);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_99);
x_125 = l_Lean_Compiler_LCNF_Code_inferType(x_99, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_118);
x_128 = l_Lean_Compiler_LCNF_mkForallParams(x_118, x_126, x_3, x_4, x_5, x_6, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_95, x_129, x_118, x_99, x_3, x_4, x_5, x_6, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_2, x_134, x_117);
x_136 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_96, x_135, x_3, x_4, x_5, x_6, x_133);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_136, 0);
lean_ctor_set(x_1, 1, x_138);
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set(x_136, 0, x_1);
return x_136;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 0);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_136);
lean_ctor_set(x_1, 1, x_139);
lean_ctor_set(x_1, 0, x_132);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_1);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
uint8_t x_142; 
lean_dec(x_132);
lean_free_object(x_1);
x_142 = !lean_is_exclusive(x_136);
if (x_142 == 0)
{
return x_136;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_136, 0);
x_144 = lean_ctor_get(x_136, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_136);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_free_object(x_1);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_128);
if (x_146 == 0)
{
return x_128;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_128, 0);
x_148 = lean_ctor_get(x_128, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_128);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_free_object(x_1);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_125);
if (x_150 == 0)
{
return x_125;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_125, 0);
x_152 = lean_ctor_get(x_125, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_125);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_99);
x_154 = l_Lean_Compiler_LCNF_Code_inferType(x_99, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_118);
x_157 = l_Lean_Compiler_LCNF_mkForallParams(x_118, x_155, x_3, x_4, x_5, x_6, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_95, x_158, x_118, x_99, x_3, x_4, x_5, x_6, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_2, x_163, x_117);
x_165 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_96, x_164, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_161);
lean_ctor_set(x_169, 1, x_166);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_161);
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_173 = x_165;
} else {
 lean_dec_ref(x_165);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = lean_ctor_get(x_157, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_157, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_177 = x_157;
} else {
 lean_dec_ref(x_157);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = lean_ctor_get(x_154, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_154, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_181 = x_154;
} else {
 lean_dec_ref(x_154);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_118);
lean_dec(x_117);
x_183 = lean_ctor_get(x_95, 3);
lean_inc(x_183);
lean_inc(x_95);
x_184 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_95, x_183, x_103, x_99, x_3, x_4, x_5, x_6, x_114);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_96);
x_187 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_96, x_2, x_3, x_4, x_5, x_6, x_186);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; size_t x_190; size_t x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_191 = lean_ptr_addr(x_189);
x_192 = lean_usize_dec_eq(x_190, x_191);
if (x_192 == 0)
{
uint8_t x_193; 
lean_dec(x_95);
x_193 = !lean_is_exclusive(x_1);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_1, 1);
lean_dec(x_194);
x_195 = lean_ctor_get(x_1, 0);
lean_dec(x_195);
lean_ctor_set(x_1, 1, x_189);
lean_ctor_set(x_1, 0, x_185);
lean_ctor_set(x_187, 0, x_1);
return x_187;
}
else
{
lean_object* x_196; 
lean_dec(x_1);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_185);
lean_ctor_set(x_196, 1, x_189);
lean_ctor_set(x_187, 0, x_196);
return x_187;
}
}
else
{
size_t x_197; size_t x_198; uint8_t x_199; 
x_197 = lean_ptr_addr(x_95);
lean_dec(x_95);
x_198 = lean_ptr_addr(x_185);
x_199 = lean_usize_dec_eq(x_197, x_198);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_1);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_1, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_1, 0);
lean_dec(x_202);
lean_ctor_set(x_1, 1, x_189);
lean_ctor_set(x_1, 0, x_185);
lean_ctor_set(x_187, 0, x_1);
return x_187;
}
else
{
lean_object* x_203; 
lean_dec(x_1);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_185);
lean_ctor_set(x_203, 1, x_189);
lean_ctor_set(x_187, 0, x_203);
return x_187;
}
}
else
{
lean_dec(x_189);
lean_dec(x_185);
lean_ctor_set(x_187, 0, x_1);
return x_187;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; size_t x_206; size_t x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_187, 0);
x_205 = lean_ctor_get(x_187, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_187);
x_206 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_207 = lean_ptr_addr(x_204);
x_208 = lean_usize_dec_eq(x_206, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_95);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_209 = x_1;
} else {
 lean_dec_ref(x_1);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(2, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_185);
lean_ctor_set(x_210, 1, x_204);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_205);
return x_211;
}
else
{
size_t x_212; size_t x_213; uint8_t x_214; 
x_212 = lean_ptr_addr(x_95);
lean_dec(x_95);
x_213 = lean_ptr_addr(x_185);
x_214 = lean_usize_dec_eq(x_212, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_215 = x_1;
} else {
 lean_dec_ref(x_1);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(2, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_185);
lean_ctor_set(x_216, 1, x_204);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_205);
return x_217;
}
else
{
lean_object* x_218; 
lean_dec(x_204);
lean_dec(x_185);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_205);
return x_218;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_185);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_187);
if (x_219 == 0)
{
return x_187;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_187, 0);
x_221 = lean_ctor_get(x_187, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_187);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = !lean_is_exclusive(x_98);
if (x_223 == 0)
{
return x_98;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_98, 0);
x_225 = lean_ctor_get(x_98, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_98);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
case 3:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
x_229 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__3(x_2, x_227);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_1);
lean_ctor_set(x_230, 1, x_7);
return x_230;
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_1);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; size_t x_241; size_t x_242; lean_object* x_243; uint8_t x_244; 
x_232 = lean_ctor_get(x_1, 1);
lean_dec(x_232);
x_233 = lean_ctor_get(x_1, 0);
lean_dec(x_233);
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_array_get_size(x_228);
x_236 = lean_unsigned_to_nat(0u);
x_237 = l_Array_toSubarray___rarg(x_228, x_236, x_235);
x_238 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_array_get_size(x_234);
x_241 = lean_usize_of_nat(x_240);
lean_dec(x_240);
x_242 = 0;
x_243 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4(x_234, x_241, x_242, x_239, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_234);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_243, 0);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_243);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
lean_ctor_set(x_1, 1, x_249);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_1);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; size_t x_258; size_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_1);
x_251 = lean_ctor_get(x_229, 0);
lean_inc(x_251);
lean_dec(x_229);
x_252 = lean_array_get_size(x_228);
x_253 = lean_unsigned_to_nat(0u);
x_254 = l_Array_toSubarray___rarg(x_228, x_253, x_252);
x_255 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_array_get_size(x_251);
x_258 = lean_usize_of_nat(x_257);
lean_dec(x_257);
x_259 = 0;
x_260 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4(x_251, x_258, x_259, x_256, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_251);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_263 = x_260;
} else {
 lean_dec_ref(x_260);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_265, 0, x_227);
lean_ctor_set(x_265, 1, x_264);
if (lean_is_scalar(x_263)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_263;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_262);
return x_266;
}
}
}
case 4:
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_1, 0);
lean_inc(x_267);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_ctor_get(x_267, 1);
x_271 = lean_ctor_get(x_267, 2);
x_272 = lean_ctor_get(x_267, 3);
x_273 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2;
lean_inc(x_272);
x_274 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__5(x_272, x_273, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; size_t x_277; size_t x_278; uint8_t x_279; 
x_276 = lean_ctor_get(x_274, 0);
x_277 = lean_ptr_addr(x_272);
lean_dec(x_272);
x_278 = lean_ptr_addr(x_276);
x_279 = lean_usize_dec_eq(x_277, x_278);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_1);
if (x_280 == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_1, 0);
lean_dec(x_281);
lean_ctor_set(x_267, 3, x_276);
lean_ctor_set(x_274, 0, x_1);
return x_274;
}
else
{
lean_object* x_282; 
lean_dec(x_1);
lean_ctor_set(x_267, 3, x_276);
x_282 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_282, 0, x_267);
lean_ctor_set(x_274, 0, x_282);
return x_274;
}
}
else
{
lean_dec(x_276);
lean_free_object(x_267);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_ctor_set(x_274, 0, x_1);
return x_274;
}
}
else
{
lean_object* x_283; lean_object* x_284; size_t x_285; size_t x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_274, 0);
x_284 = lean_ctor_get(x_274, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_274);
x_285 = lean_ptr_addr(x_272);
lean_dec(x_272);
x_286 = lean_ptr_addr(x_283);
x_287 = lean_usize_dec_eq(x_285, x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_288 = x_1;
} else {
 lean_dec_ref(x_1);
 x_288 = lean_box(0);
}
lean_ctor_set(x_267, 3, x_283);
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(4, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_267);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_284);
return x_290;
}
else
{
lean_object* x_291; 
lean_dec(x_283);
lean_free_object(x_267);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_1);
lean_ctor_set(x_291, 1, x_284);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_free_object(x_267);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_274);
if (x_292 == 0)
{
return x_274;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_274, 0);
x_294 = lean_ctor_get(x_274, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_274);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_267, 0);
x_297 = lean_ctor_get(x_267, 1);
x_298 = lean_ctor_get(x_267, 2);
x_299 = lean_ctor_get(x_267, 3);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_267);
x_300 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2;
lean_inc(x_299);
x_301 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__5(x_299, x_300, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; size_t x_305; size_t x_306; uint8_t x_307; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_305 = lean_ptr_addr(x_299);
lean_dec(x_299);
x_306 = lean_ptr_addr(x_302);
x_307 = lean_usize_dec_eq(x_305, x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_308 = x_1;
} else {
 lean_dec_ref(x_1);
 x_308 = lean_box(0);
}
x_309 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_309, 0, x_296);
lean_ctor_set(x_309, 1, x_297);
lean_ctor_set(x_309, 2, x_298);
lean_ctor_set(x_309, 3, x_302);
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(4, 1, 0);
} else {
 x_310 = x_308;
}
lean_ctor_set(x_310, 0, x_309);
if (lean_is_scalar(x_304)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_304;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_303);
return x_311;
}
else
{
lean_object* x_312; 
lean_dec(x_302);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
if (lean_is_scalar(x_304)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_304;
}
lean_ctor_set(x_312, 0, x_1);
lean_ctor_set(x_312, 1, x_303);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_1);
x_313 = lean_ctor_get(x_301, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_301, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_315 = x_301;
} else {
 lean_dec_ref(x_301);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
}
default: 
{
lean_object* x_317; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_1);
lean_ctor_set(x_317, 1, x_7);
return x_317;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__1___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceJpArity_reduce___spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_12, x_14, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 4, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 4, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_32 = lean_ctor_get(x_1, 5);
lean_inc(x_32);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_29, x_33, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 1, x_31);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceJpArity", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_reduceJpArity___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceJpArity), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_reduceJpArity___closed__2;
x_3 = l_Lean_Compiler_LCNF_reduceJpArity___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_LCNF_reduceJpArity(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1;
x_2 = l_Lean_Compiler_LCNF_reduceJpArity___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ReduceJpArity", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__16;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__18;
x_2 = lean_unsigned_to_nat(887u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__2;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__19;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2);
l_Lean_Compiler_LCNF_reduceJpArity___closed__1 = _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceJpArity___closed__1);
l_Lean_Compiler_LCNF_reduceJpArity___closed__2 = _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceJpArity___closed__2);
l_Lean_Compiler_LCNF_reduceJpArity___closed__3 = _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceJpArity___closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__18);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__19 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887____closed__19);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_887_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
