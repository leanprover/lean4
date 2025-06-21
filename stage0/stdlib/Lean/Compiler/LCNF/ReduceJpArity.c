// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceJpArity
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.PassManager
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
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceJpArity___closed__2;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceJpArity___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6;
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceJpArity___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; uint8_t x_41; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_array_uget(x_1, x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = lean_array_get_size(x_23);
x_28 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_25);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_23, x_39);
lean_dec(x_23);
x_41 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_25, x_40);
lean_dec(x_40);
lean_dec(x_25);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_26);
x_42 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_24, x_5, x_6);
lean_dec(x_24);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(x_41);
x_45 = lean_array_push(x_18, x_44);
lean_ctor_set(x_4, 0, x_45);
x_7 = x_4;
x_8 = x_43;
goto block_12;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_26, x_16);
lean_dec(x_26);
x_47 = lean_box(x_41);
x_48 = lean_array_push(x_18, x_47);
x_49 = lean_array_push(x_21, x_24);
lean_ctor_set(x_15, 1, x_46);
lean_ctor_set(x_15, 0, x_49);
lean_ctor_set(x_4, 0, x_48);
x_7 = x_4;
x_8 = x_6;
goto block_12;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_50 = lean_ctor_get(x_15, 0);
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
x_52 = lean_array_uget(x_1, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
x_55 = lean_array_get_size(x_51);
x_56 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_53);
x_57 = 32;
x_58 = lean_uint64_shift_right(x_56, x_57);
x_59 = lean_uint64_xor(x_56, x_58);
x_60 = 16;
x_61 = lean_uint64_shift_right(x_59, x_60);
x_62 = lean_uint64_xor(x_59, x_61);
x_63 = lean_uint64_to_usize(x_62);
x_64 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_65 = 1;
x_66 = lean_usize_sub(x_64, x_65);
x_67 = lean_usize_land(x_63, x_66);
x_68 = lean_array_uget(x_51, x_67);
lean_dec(x_51);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_53, x_68);
lean_dec(x_68);
lean_dec(x_53);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_54);
x_70 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_52, x_5, x_6);
lean_dec(x_52);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(x_69);
x_73 = lean_array_push(x_18, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_50);
lean_ctor_set(x_74, 1, x_16);
lean_ctor_set(x_4, 1, x_74);
lean_ctor_set(x_4, 0, x_73);
x_7 = x_4;
x_8 = x_71;
goto block_12;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_54, x_16);
lean_dec(x_54);
x_76 = lean_box(x_69);
x_77 = lean_array_push(x_18, x_76);
x_78 = lean_array_push(x_50, x_52);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_4, 1, x_79);
lean_ctor_set(x_4, 0, x_77);
x_7 = x_4;
x_8 = x_6;
goto block_12;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; size_t x_95; size_t x_96; size_t x_97; size_t x_98; size_t x_99; lean_object* x_100; uint8_t x_101; 
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
lean_dec(x_4);
x_81 = lean_ctor_get(x_15, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_82 = x_15;
} else {
 lean_dec_ref(x_15);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_16, 1);
lean_inc(x_83);
x_84 = lean_array_uget(x_1, x_3);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 2);
lean_inc(x_86);
x_87 = lean_array_get_size(x_83);
x_88 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_85);
x_89 = 32;
x_90 = lean_uint64_shift_right(x_88, x_89);
x_91 = lean_uint64_xor(x_88, x_90);
x_92 = 16;
x_93 = lean_uint64_shift_right(x_91, x_92);
x_94 = lean_uint64_xor(x_91, x_93);
x_95 = lean_uint64_to_usize(x_94);
x_96 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_97 = 1;
x_98 = lean_usize_sub(x_96, x_97);
x_99 = lean_usize_land(x_95, x_98);
x_100 = lean_array_uget(x_83, x_99);
lean_dec(x_83);
x_101 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_85, x_100);
lean_dec(x_100);
lean_dec(x_85);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_86);
x_102 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_84, x_5, x_6);
lean_dec(x_84);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(x_101);
x_105 = lean_array_push(x_80, x_104);
if (lean_is_scalar(x_82)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_82;
}
lean_ctor_set(x_106, 0, x_81);
lean_ctor_set(x_106, 1, x_16);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_7 = x_107;
x_8 = x_103;
goto block_12;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_86, x_16);
lean_dec(x_86);
x_109 = lean_box(x_101);
x_110 = lean_array_push(x_80, x_109);
x_111 = lean_array_push(x_81, x_84);
if (lean_is_scalar(x_82)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_82;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_7 = x_113;
x_8 = x_6;
goto block_12;
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_1, x_3);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_18, x_28);
lean_inc(x_17);
lean_ctor_set(x_15, 1, x_29);
if (x_27 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_31 = lean_array_push(x_16, x_30);
lean_ctor_set(x_4, 1, x_31);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
x_32 = lean_array_uget(x_1, x_3);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_18, x_34);
lean_inc(x_17);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_19);
if (x_33 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_36);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_array_fget(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_38 = lean_array_push(x_16, x_37);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_36);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
x_48 = lean_array_uget(x_1, x_3);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_42, x_50);
lean_inc(x_41);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_43);
if (x_49 == 0)
{
lean_object* x_53; 
lean_dec(x_42);
lean_dec(x_41);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
x_6 = x_53;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_array_fget(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_55 = lean_array_push(x_40, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_6 = x_56;
x_7 = x_5;
goto block_11;
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
x_13 = x_33;
goto block_32;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_13 = x_34;
goto block_32;
}
block_32:
{
lean_object* x_14; 
lean_inc(x_3);
x_14 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_15);
x_18 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = lean_array_fset(x_2, x_1, x_17);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_23;
x_8 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
lean_dec(x_1);
x_1 = x_26;
x_8 = x_16;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; size_t x_23; size_t x_24; uint8_t x_25; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_23 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_24 = lean_ptr_addr(x_11);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
x_14 = x_25;
goto block_22;
}
else
{
size_t x_26; uint8_t x_27; 
x_26 = lean_ptr_addr(x_8);
x_27 = lean_usize_dec_eq(x_26, x_26);
x_14 = x_27;
goto block_22;
}
block_22:
{
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_11);
if (lean_is_scalar(x_13)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_13;
}
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
if (lean_is_scalar(x_13)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_13;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 4);
lean_inc(x_32);
lean_inc(x_2);
x_33 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_28);
x_36 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_28, x_31, x_30, x_34, x_4, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_29);
x_39 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_29, x_2, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; size_t x_52; size_t x_53; uint8_t x_54; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_52 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_53 = lean_ptr_addr(x_40);
x_54 = lean_usize_dec_eq(x_52, x_53);
if (x_54 == 0)
{
lean_dec(x_28);
x_43 = x_54;
goto block_51;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_56 = lean_ptr_addr(x_37);
x_57 = lean_usize_dec_eq(x_55, x_56);
x_43 = x_57;
goto block_51;
}
block_51:
{
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_37);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_40);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_40);
lean_dec(x_37);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 4);
lean_inc(x_62);
lean_inc(x_2);
x_63 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_62, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4;
lean_inc(x_65);
x_68 = l_Lean_Compiler_LCNF_Code_collectUsed(x_65, x_67);
x_69 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5;
lean_inc(x_60);
x_70 = l_Array_reverse___redArg(x_60);
lean_ctor_set(x_63, 1, x_68);
lean_ctor_set(x_63, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_63);
x_72 = lean_array_size(x_70);
x_73 = 0;
x_74 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_70, x_72, x_73, x_71, x_4, x_66);
lean_dec(x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Array_reverse___redArg(x_79);
x_81 = lean_array_get_size(x_80);
x_82 = lean_array_get_size(x_60);
x_83 = lean_nat_dec_eq(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_61);
lean_dec(x_60);
x_84 = !lean_is_exclusive(x_1);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_1, 0);
lean_dec(x_86);
lean_inc(x_65);
x_87 = l_Lean_Compiler_LCNF_Code_inferType(x_65, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_80);
x_90 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_80, x_88, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_91, x_80, x_65, x_4, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = l_Array_reverse___redArg(x_78);
x_98 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_96, x_97);
x_99 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_98, x_3, x_4, x_5, x_6, x_95);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_ctor_set(x_1, 1, x_101);
lean_ctor_set(x_1, 0, x_94);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_99);
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_94);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_dec(x_94);
lean_free_object(x_1);
return x_99;
}
}
else
{
uint8_t x_105; 
lean_free_object(x_1);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_90);
if (x_105 == 0)
{
return x_90;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_90, 0);
x_107 = lean_ctor_get(x_90, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_90);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_free_object(x_1);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_87);
if (x_109 == 0)
{
return x_87;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_87, 0);
x_111 = lean_ctor_get(x_87, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_87);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_1);
lean_inc(x_65);
x_113 = l_Lean_Compiler_LCNF_Code_inferType(x_65, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_80);
x_116 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_80, x_114, x_3, x_4, x_5, x_6, x_115);
lean_dec(x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_117, x_80, x_65, x_4, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = l_Array_reverse___redArg(x_78);
x_124 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_122, x_123);
x_125 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_124, x_3, x_4, x_5, x_6, x_121);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_126);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
lean_dec(x_120);
return x_125;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_135 = lean_ctor_get(x_113, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_113, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_137 = x_113;
} else {
 lean_dec_ref(x_113);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_80);
lean_dec(x_78);
lean_inc(x_58);
x_139 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_61, x_60, x_65, x_4, x_77);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_59);
x_142 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_2, x_3, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; size_t x_155; size_t x_156; uint8_t x_157; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_155 = lean_ptr_addr(x_59);
lean_dec(x_59);
x_156 = lean_ptr_addr(x_143);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_dec(x_58);
x_146 = x_157;
goto block_154;
}
else
{
size_t x_158; size_t x_159; uint8_t x_160; 
x_158 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_159 = lean_ptr_addr(x_140);
x_160 = lean_usize_dec_eq(x_158, x_159);
x_146 = x_160;
goto block_154;
}
block_154:
{
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_1);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_1, 1);
lean_dec(x_148);
x_149 = lean_ctor_get(x_1, 0);
lean_dec(x_149);
lean_ctor_set(x_1, 1, x_143);
lean_ctor_set(x_1, 0, x_140);
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_1);
lean_ctor_set(x_150, 1, x_144);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_1);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_140);
lean_ctor_set(x_151, 1, x_143);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_140);
if (lean_is_scalar(x_145)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_145;
}
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_144);
return x_153;
}
}
}
else
{
lean_dec(x_140);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
return x_142;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_161 = lean_ctor_get(x_63, 0);
x_162 = lean_ctor_get(x_63, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_63);
x_163 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4;
lean_inc(x_161);
x_164 = l_Lean_Compiler_LCNF_Code_collectUsed(x_161, x_163);
x_165 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5;
lean_inc(x_60);
x_166 = l_Array_reverse___redArg(x_60);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_164);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_array_size(x_166);
x_170 = 0;
x_171 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_166, x_169, x_170, x_168, x_4, x_162);
lean_dec(x_166);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
lean_dec(x_173);
x_177 = l_Array_reverse___redArg(x_176);
x_178 = lean_array_get_size(x_177);
x_179 = lean_array_get_size(x_60);
x_180 = lean_nat_dec_eq(x_178, x_179);
lean_dec(x_179);
lean_dec(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_181 = x_1;
} else {
 lean_dec_ref(x_1);
 x_181 = lean_box(0);
}
lean_inc(x_161);
x_182 = l_Lean_Compiler_LCNF_Code_inferType(x_161, x_3, x_4, x_5, x_6, x_174);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_177);
x_185 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_177, x_183, x_3, x_4, x_5, x_6, x_184);
lean_dec(x_183);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_186, x_177, x_161, x_4, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = l_Array_reverse___redArg(x_175);
x_193 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_191, x_192);
x_194 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_193, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_198 = lean_alloc_ctor(2, 2, 0);
} else {
 x_198 = x_181;
}
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_195);
if (lean_is_scalar(x_197)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_197;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_196);
return x_199;
}
else
{
lean_dec(x_189);
lean_dec(x_181);
return x_194;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_161);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_200 = lean_ctor_get(x_185, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_185, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_202 = x_185;
} else {
 lean_dec_ref(x_185);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_161);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_204 = lean_ctor_get(x_182, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_206 = x_182;
} else {
 lean_dec_ref(x_182);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_177);
lean_dec(x_175);
lean_inc(x_58);
x_208 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_61, x_60, x_161, x_4, x_174);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_59);
x_211 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_2, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; size_t x_221; size_t x_222; uint8_t x_223; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_221 = lean_ptr_addr(x_59);
lean_dec(x_59);
x_222 = lean_ptr_addr(x_212);
x_223 = lean_usize_dec_eq(x_221, x_222);
if (x_223 == 0)
{
lean_dec(x_58);
x_215 = x_223;
goto block_220;
}
else
{
size_t x_224; size_t x_225; uint8_t x_226; 
x_224 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_225 = lean_ptr_addr(x_209);
x_226 = lean_usize_dec_eq(x_224, x_225);
x_215 = x_226;
goto block_220;
}
block_220:
{
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_216 = x_1;
} else {
 lean_dec_ref(x_1);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(2, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_212);
if (lean_is_scalar(x_214)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_214;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
else
{
lean_object* x_219; 
lean_dec(x_212);
lean_dec(x_209);
if (lean_is_scalar(x_214)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_214;
}
lean_ctor_set(x_219, 0, x_1);
lean_ctor_set(x_219, 1, x_213);
return x_219;
}
}
}
else
{
lean_dec(x_209);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
return x_211;
}
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
case 3:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
x_229 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(x_2, x_227);
lean_dec(x_2);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
lean_dec(x_228);
lean_dec(x_227);
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
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; lean_object* x_242; uint8_t x_243; 
x_232 = lean_ctor_get(x_1, 1);
lean_dec(x_232);
x_233 = lean_ctor_get(x_1, 0);
lean_dec(x_233);
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_unsigned_to_nat(0u);
x_236 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6;
x_237 = lean_array_get_size(x_228);
x_238 = l_Array_toSubarray___redArg(x_228, x_235, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
x_240 = lean_array_size(x_234);
x_241 = 0;
x_242 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_234, x_240, x_241, x_239, x_7);
lean_dec(x_234);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_242, 0);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_242, 0, x_1);
return x_242;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_242, 0);
x_247 = lean_ctor_get(x_242, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_242);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
lean_ctor_set(x_1, 1, x_248);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; size_t x_256; size_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_1);
x_250 = lean_ctor_get(x_229, 0);
lean_inc(x_250);
lean_dec(x_229);
x_251 = lean_unsigned_to_nat(0u);
x_252 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6;
x_253 = lean_array_get_size(x_228);
x_254 = l_Array_toSubarray___redArg(x_228, x_251, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
x_256 = lean_array_size(x_250);
x_257 = 0;
x_258 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_250, x_256, x_257, x_255, x_7);
lean_dec(x_250);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec(x_259);
x_263 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_263, 0, x_227);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_261)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_261;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_260);
return x_264;
}
}
}
case 4:
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_1, 0);
lean_inc(x_265);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_265, 0);
x_268 = lean_ctor_get(x_265, 1);
x_269 = lean_ctor_get(x_265, 2);
x_270 = lean_ctor_get(x_265, 3);
x_271 = lean_unsigned_to_nat(0u);
lean_inc(x_270);
x_272 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(x_271, x_270, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; size_t x_275; size_t x_276; uint8_t x_277; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_ptr_addr(x_270);
lean_dec(x_270);
x_276 = lean_ptr_addr(x_274);
x_277 = lean_usize_dec_eq(x_275, x_276);
if (x_277 == 0)
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_1);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_1, 0);
lean_dec(x_279);
lean_ctor_set(x_265, 3, x_274);
lean_ctor_set(x_272, 0, x_1);
return x_272;
}
else
{
lean_object* x_280; 
lean_dec(x_1);
lean_ctor_set(x_265, 3, x_274);
x_280 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_280, 0, x_265);
lean_ctor_set(x_272, 0, x_280);
return x_272;
}
}
else
{
lean_dec(x_274);
lean_free_object(x_265);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_ctor_set(x_272, 0, x_1);
return x_272;
}
}
else
{
lean_object* x_281; lean_object* x_282; size_t x_283; size_t x_284; uint8_t x_285; 
x_281 = lean_ctor_get(x_272, 0);
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_272);
x_283 = lean_ptr_addr(x_270);
lean_dec(x_270);
x_284 = lean_ptr_addr(x_281);
x_285 = lean_usize_dec_eq(x_283, x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_286 = x_1;
} else {
 lean_dec_ref(x_1);
 x_286 = lean_box(0);
}
lean_ctor_set(x_265, 3, x_281);
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(4, 1, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_265);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_282);
return x_288;
}
else
{
lean_object* x_289; 
lean_dec(x_281);
lean_free_object(x_265);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_1);
lean_ctor_set(x_289, 1, x_282);
return x_289;
}
}
}
else
{
uint8_t x_290; 
lean_free_object(x_265);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_272);
if (x_290 == 0)
{
return x_272;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_272, 0);
x_292 = lean_ctor_get(x_272, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_272);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_265, 0);
x_295 = lean_ctor_get(x_265, 1);
x_296 = lean_ctor_get(x_265, 2);
x_297 = lean_ctor_get(x_265, 3);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_265);
x_298 = lean_unsigned_to_nat(0u);
lean_inc(x_297);
x_299 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(x_298, x_297, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; size_t x_303; size_t x_304; uint8_t x_305; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = lean_ptr_addr(x_297);
lean_dec(x_297);
x_304 = lean_ptr_addr(x_300);
x_305 = lean_usize_dec_eq(x_303, x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_306 = x_1;
} else {
 lean_dec_ref(x_1);
 x_306 = lean_box(0);
}
x_307 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_307, 0, x_294);
lean_ctor_set(x_307, 1, x_295);
lean_ctor_set(x_307, 2, x_296);
lean_ctor_set(x_307, 3, x_300);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(4, 1, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
if (lean_is_scalar(x_302)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_302;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_301);
return x_309;
}
else
{
lean_object* x_310; 
lean_dec(x_300);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
if (lean_is_scalar(x_302)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_302;
}
lean_ctor_set(x_310, 0, x_1);
lean_ctor_set(x_310, 1, x_301);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_1);
x_311 = lean_ctor_get(x_299, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_299, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_313 = x_299;
} else {
 lean_dec_ref(x_299);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
default: 
{
lean_object* x_315; 
lean_dec(x_2);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_1);
lean_ctor_set(x_315, 1, x_7);
return x_315;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0;
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(x_14, x_12, x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_1, 4, x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 4, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_33 = lean_ctor_get(x_1, 5);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_34 = l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0;
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(x_34, x_30, x_35, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_33);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 1, x_32);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceJpArity", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reduceJpArity___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__2() {
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
x_2 = l_Lean_Compiler_LCNF_reduceJpArity___closed__1;
x_3 = l_Lean_Compiler_LCNF_reduceJpArity___closed__2;
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_reduceJpArity___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ReduceJpArity", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(879u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__3 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__3);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__4);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__5);
l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6 = _init_l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__6);
l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0);
l_Lean_Compiler_LCNF_reduceJpArity___closed__0 = _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceJpArity___closed__0);
l_Lean_Compiler_LCNF_reduceJpArity___closed__1 = _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceJpArity___closed__1);
l_Lean_Compiler_LCNF_reduceJpArity___closed__2 = _init_l_Lean_Compiler_LCNF_reduceJpArity___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceJpArity___closed__2);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
