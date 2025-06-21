// Lean compiler output
// Module: Lean.Compiler.LCNF.Closure
// Imports: Lean.Util.ForEachExprWhere Lean.Compiler.LCNF.CompilerM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectType___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__5;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Closure_collectType___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_mod(size_t, size_t);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_findParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_17, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__1(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_16, x_33);
lean_dec(x_16);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_31);
x_37 = lean_array_uset(x_17, x_30, x_36);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_mul(x_34, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__2(x_37);
lean_ctor_set(x_11, 1, x_44);
lean_ctor_set(x_11, 0, x_34);
x_45 = lean_st_ref_set(x_3, x_10, x_12);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_35);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_ctor_set(x_11, 1, x_37);
lean_ctor_set(x_11, 0, x_34);
x_50 = lean_st_ref_set(x_3, x_10, x_12);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_35);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_31);
lean_dec(x_1);
x_55 = lean_st_ref_set(x_3, x_10, x_12);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_box(0);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_62 = lean_ctor_get(x_11, 0);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_11);
x_64 = lean_array_get_size(x_63);
x_65 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_66 = 32;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = 16;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = lean_uint64_to_usize(x_71);
x_73 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_74 = 1;
x_75 = lean_usize_sub(x_73, x_74);
x_76 = lean_usize_land(x_72, x_75);
x_77 = lean_array_uget(x_63, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__1(x_1, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_62, x_79);
lean_dec(x_62);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_77);
x_83 = lean_array_uset(x_63, x_76, x_82);
x_84 = lean_unsigned_to_nat(4u);
x_85 = lean_nat_mul(x_80, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__2(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_10, 0, x_91);
x_92 = lean_st_ref_set(x_3, x_10, x_12);
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
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_81);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_80);
lean_ctor_set(x_96, 1, x_83);
lean_ctor_set(x_10, 0, x_96);
x_97 = lean_st_ref_set(x_3, x_10, x_12);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_81);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_dec(x_1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_62);
lean_ctor_set(x_101, 1, x_63);
lean_ctor_set(x_10, 0, x_101);
x_102 = lean_st_ref_set(x_3, x_10, x_12);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; size_t x_120; size_t x_121; size_t x_122; size_t x_123; size_t x_124; lean_object* x_125; uint8_t x_126; 
x_107 = lean_ctor_get(x_10, 1);
x_108 = lean_ctor_get(x_10, 2);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_10);
x_109 = lean_ctor_get(x_11, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_111 = x_11;
} else {
 lean_dec_ref(x_11);
 x_111 = lean_box(0);
}
x_112 = lean_array_get_size(x_110);
x_113 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_114 = 32;
x_115 = lean_uint64_shift_right(x_113, x_114);
x_116 = lean_uint64_xor(x_113, x_115);
x_117 = 16;
x_118 = lean_uint64_shift_right(x_116, x_117);
x_119 = lean_uint64_xor(x_116, x_118);
x_120 = lean_uint64_to_usize(x_119);
x_121 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_122 = 1;
x_123 = lean_usize_sub(x_121, x_122);
x_124 = lean_usize_land(x_120, x_123);
x_125 = lean_array_uget(x_110, x_124);
x_126 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__1(x_1, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_add(x_109, x_127);
lean_dec(x_109);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_125);
x_131 = lean_array_uset(x_110, x_124, x_130);
x_132 = lean_unsigned_to_nat(4u);
x_133 = lean_nat_mul(x_128, x_132);
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_nat_div(x_133, x_134);
lean_dec(x_133);
x_136 = lean_array_get_size(x_131);
x_137 = lean_nat_dec_le(x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__2(x_131);
if (lean_is_scalar(x_111)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_111;
}
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_107);
lean_ctor_set(x_140, 2, x_108);
x_141 = lean_st_ref_set(x_3, x_140, x_12);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_129);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
if (lean_is_scalar(x_111)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_111;
}
lean_ctor_set(x_145, 0, x_128);
lean_ctor_set(x_145, 1, x_131);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_107);
lean_ctor_set(x_146, 2, x_108);
x_147 = lean_st_ref_set(x_3, x_146, x_12);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_129);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_125);
lean_dec(x_1);
if (lean_is_scalar(x_111)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_111;
}
lean_ctor_set(x_151, 0, x_109);
lean_ctor_set(x_151, 1, x_110);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_107);
lean_ctor_set(x_152, 2, x_108);
x_153 = lean_st_ref_set(x_3, x_152, x_12);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_15, x_16, x_14, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_9, x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(x_1, x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ptr_addr(x_1);
x_15 = 8191;
x_16 = lean_usize_mod(x_14, x_15);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_array_uget(x_17, x_16);
lean_dec(x_17);
x_19 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_20 = lean_usize_dec_eq(x_19, x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
x_21 = lean_st_ref_take(x_2, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_array_uset(x_25, x_16, x_1);
lean_ctor_set(x_22, 0, x_26);
x_27 = lean_st_ref_set(x_2, x_22, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_array_uset(x_36, x_16, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_st_ref_set(x_2, x_39, x_23);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = 0;
x_44 = lean_box(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
uint8_t x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_10, 0, x_47);
return x_10;
}
}
else
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; size_t x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_ptr_addr(x_1);
x_51 = 8191;
x_52 = lean_usize_mod(x_50, x_51);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_array_uget(x_53, x_52);
lean_dec(x_53);
x_55 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_56 = lean_usize_dec_eq(x_55, x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_st_ref_take(x_2, x_49);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_array_uset(x_60, x_52, x_1);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_st_ref_set(x_2, x_64, x_59);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = 0;
x_69 = lean_box(x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_49);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Expr_hash(x_1);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_16, x_29);
lean_dec(x_16);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_10);
x_32 = lean_st_ref_take(x_2, x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_usize_sub(x_42, x_27);
x_44 = lean_usize_land(x_25, x_43);
x_45 = lean_array_uget(x_40, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_39, x_47);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_45);
x_51 = lean_array_uset(x_40, x_44, x_50);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_mul(x_48, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_51);
lean_ctor_set(x_34, 1, x_58);
lean_ctor_set(x_34, 0, x_48);
x_59 = lean_st_ref_set(x_2, x_33, x_35);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = 0;
x_63 = lean_box(x_62);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec(x_59);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_ctor_set(x_34, 1, x_51);
lean_ctor_set(x_34, 0, x_48);
x_68 = lean_st_ref_set(x_2, x_33, x_35);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = 0;
x_72 = lean_box(x_71);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_45);
lean_dec(x_1);
x_77 = lean_st_ref_set(x_2, x_33, x_35);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = 0;
x_81 = lean_box(x_80);
lean_ctor_set(x_77, 0, x_81);
return x_77;
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_34, 0);
x_87 = lean_ctor_get(x_34, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_34);
x_88 = lean_array_get_size(x_87);
x_89 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_90 = lean_usize_sub(x_89, x_27);
x_91 = lean_usize_land(x_25, x_90);
x_92 = lean_array_uget(x_87, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_86, x_94);
lean_dec(x_86);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_92);
x_98 = lean_array_uset(x_87, x_91, x_97);
x_99 = lean_unsigned_to_nat(4u);
x_100 = lean_nat_mul(x_95, x_99);
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_nat_div(x_100, x_101);
lean_dec(x_100);
x_103 = lean_array_get_size(x_98);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_105 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_98);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_33, 1, x_106);
x_107 = lean_st_ref_set(x_2, x_33, x_35);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = 0;
x_111 = lean_box(x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_95);
lean_ctor_set(x_113, 1, x_98);
lean_ctor_set(x_33, 1, x_113);
x_114 = lean_st_ref_set(x_2, x_33, x_35);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = 0;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_92);
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_86);
lean_ctor_set(x_120, 1, x_87);
lean_ctor_set(x_33, 1, x_120);
x_121 = lean_st_ref_set(x_2, x_33, x_35);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = 0;
x_125 = lean_box(x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; uint8_t x_136; 
x_127 = lean_ctor_get(x_33, 0);
lean_inc(x_127);
lean_dec(x_33);
x_128 = lean_ctor_get(x_34, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_34, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_130 = x_34;
} else {
 lean_dec_ref(x_34);
 x_130 = lean_box(0);
}
x_131 = lean_array_get_size(x_129);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = lean_usize_sub(x_132, x_27);
x_134 = lean_usize_land(x_25, x_133);
x_135 = lean_array_uget(x_129, x_134);
x_136 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_128, x_137);
lean_dec(x_128);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_135);
x_141 = lean_array_uset(x_129, x_134, x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = lean_nat_mul(x_138, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_141);
if (lean_is_scalar(x_130)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_130;
}
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_127);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_st_ref_set(x_2, x_150, x_35);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = 0;
x_155 = lean_box(x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
if (lean_is_scalar(x_130)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_130;
}
lean_ctor_set(x_157, 0, x_138);
lean_ctor_set(x_157, 1, x_141);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_127);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_st_ref_set(x_2, x_158, x_35);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = 0;
x_163 = lean_box(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_135);
lean_dec(x_1);
if (lean_is_scalar(x_130)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_130;
}
lean_ctor_set(x_165, 0, x_128);
lean_ctor_set(x_165, 1, x_129);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_127);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_st_ref_set(x_2, x_166, x_35);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = 0;
x_171 = lean_box(x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
}
}
else
{
uint8_t x_173; lean_object* x_174; 
lean_dec(x_1);
x_173 = 1;
x_174 = lean_box(x_173);
lean_ctor_set(x_10, 0, x_174);
return x_10;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; size_t x_185; size_t x_186; size_t x_187; size_t x_188; size_t x_189; lean_object* x_190; uint8_t x_191; 
x_175 = lean_ctor_get(x_10, 1);
lean_inc(x_175);
lean_dec(x_10);
x_176 = lean_ctor_get(x_12, 1);
lean_inc(x_176);
lean_dec(x_12);
x_177 = lean_array_get_size(x_176);
x_178 = l_Lean_Expr_hash(x_1);
x_179 = 32;
x_180 = lean_uint64_shift_right(x_178, x_179);
x_181 = lean_uint64_xor(x_178, x_180);
x_182 = 16;
x_183 = lean_uint64_shift_right(x_181, x_182);
x_184 = lean_uint64_xor(x_181, x_183);
x_185 = lean_uint64_to_usize(x_184);
x_186 = lean_usize_of_nat(x_177);
lean_dec(x_177);
x_187 = 1;
x_188 = lean_usize_sub(x_186, x_187);
x_189 = lean_usize_land(x_185, x_188);
x_190 = lean_array_uget(x_176, x_189);
lean_dec(x_176);
x_191 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; size_t x_202; size_t x_203; size_t x_204; lean_object* x_205; uint8_t x_206; 
x_192 = lean_st_ref_take(x_2, x_175);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_197 = x_193;
} else {
 lean_dec_ref(x_193);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
x_201 = lean_array_get_size(x_199);
x_202 = lean_usize_of_nat(x_201);
lean_dec(x_201);
x_203 = lean_usize_sub(x_202, x_187);
x_204 = lean_usize_land(x_185, x_203);
x_205 = lean_array_uget(x_199, x_204);
x_206 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_add(x_198, x_207);
lean_dec(x_198);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_1);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_205);
x_211 = lean_array_uset(x_199, x_204, x_210);
x_212 = lean_unsigned_to_nat(4u);
x_213 = lean_nat_mul(x_208, x_212);
x_214 = lean_unsigned_to_nat(3u);
x_215 = lean_nat_div(x_213, x_214);
lean_dec(x_213);
x_216 = lean_array_get_size(x_211);
x_217 = lean_nat_dec_le(x_215, x_216);
lean_dec(x_216);
lean_dec(x_215);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_218 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_211);
if (lean_is_scalar(x_200)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_200;
}
lean_ctor_set(x_219, 0, x_208);
lean_ctor_set(x_219, 1, x_218);
if (lean_is_scalar(x_197)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_197;
}
lean_ctor_set(x_220, 0, x_196);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_st_ref_set(x_2, x_220, x_195);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
x_224 = 0;
x_225 = lean_box(x_224);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_222);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
if (lean_is_scalar(x_200)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_200;
}
lean_ctor_set(x_227, 0, x_208);
lean_ctor_set(x_227, 1, x_211);
if (lean_is_scalar(x_197)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_197;
}
lean_ctor_set(x_228, 0, x_196);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_st_ref_set(x_2, x_228, x_195);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
x_232 = 0;
x_233 = lean_box(x_232);
if (lean_is_scalar(x_231)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_231;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_230);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_205);
lean_dec(x_1);
if (lean_is_scalar(x_200)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_200;
}
lean_ctor_set(x_235, 0, x_198);
lean_ctor_set(x_235, 1, x_199);
if (lean_is_scalar(x_197)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_197;
}
lean_ctor_set(x_236, 0, x_196);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_st_ref_set(x_2, x_236, x_195);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = 0;
x_241 = lean_box(x_240);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_239;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
return x_242;
}
}
else
{
uint8_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_1);
x_243 = 1;
x_244 = lean_box(x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_175);
return x_245;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_44 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 10:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
x_58 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_58;
}
case 11:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_59, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_60;
}
default: 
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_13);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
x_13 = l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_4);
x_17 = lean_apply_1(x_1, x_4);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_4, x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_4);
x_21 = l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_25 = lean_apply_8(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
if (x_3 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_4, x_1, x_2, x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_box(0);
x_41 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_4, x_1, x_2, x_3, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_13, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_ForEachExprWhere_initCache;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_1, x_2, x_4, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_fvarId_x21(x_1);
x_10 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectType___closed__1;
x_10 = l_Lean_Compiler_LCNF_Closure_collectType___closed__2;
x_11 = 0;
x_12 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_9, x_10, x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Closure", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Closure.collectFVar", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
x_2 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
x_3 = lean_unsigned_to_nat(151u);
x_4 = lean_unsigned_to_nat(10u);
x_5 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
lean_dec(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__1(x_1, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_free_object(x_9);
lean_inc(x_1);
x_31 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_inc(x_1);
x_36 = lean_apply_1(x_35, x_1);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_31);
x_39 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_49 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 3);
lean_inc(x_56);
x_57 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_58 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_59 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_55);
x_60 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_57, x_58, x_55, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_inc(x_53);
x_64 = lean_apply_1(x_63, x_53);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_inc(x_3);
x_66 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_3, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_69, 2);
lean_ctor_set_tag(x_46, 0);
x_73 = lean_array_push(x_72, x_46);
lean_ctor_set(x_69, 2, x_73);
x_74 = lean_st_ref_set(x_3, x_69, x_70);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
x_83 = lean_ctor_get(x_69, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
lean_ctor_set_tag(x_46, 0);
x_84 = lean_array_push(x_83, x_46);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_85, 2, x_84);
x_86 = lean_st_ref_set(x_3, x_85, x_70);
lean_dec(x_3);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_free_object(x_46);
lean_dec(x_51);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_66);
if (x_91 == 0)
{
return x_66;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_66, 0);
x_93 = lean_ctor_get(x_66, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_66);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_56);
lean_free_object(x_46);
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_95 = lean_st_ref_take(x_3, x_62);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_96, 1);
x_100 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_100, 0, x_53);
lean_ctor_set(x_100, 1, x_54);
lean_ctor_set(x_100, 2, x_55);
lean_ctor_set_uint8(x_100, sizeof(void*)*3, x_59);
x_101 = lean_array_push(x_99, x_100);
lean_ctor_set(x_96, 1, x_101);
x_102 = lean_st_ref_set(x_3, x_96, x_97);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_ctor_set(x_102, 0, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_109 = lean_ctor_get(x_96, 0);
x_110 = lean_ctor_get(x_96, 1);
x_111 = lean_ctor_get(x_96, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_96);
x_112 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_112, 0, x_53);
lean_ctor_set(x_112, 1, x_54);
lean_ctor_set(x_112, 2, x_55);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_59);
x_113 = lean_array_push(x_110, x_112);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_111);
x_115 = lean_st_ref_set(x_3, x_114, x_97);
lean_dec(x_3);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_56);
lean_free_object(x_46);
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_120 = lean_ctor_get(x_60, 1);
lean_inc(x_120);
lean_dec(x_60);
x_121 = lean_st_ref_take(x_3, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_126, 0, x_53);
lean_ctor_set(x_126, 1, x_54);
lean_ctor_set(x_126, 2, x_55);
lean_ctor_set_uint8(x_126, sizeof(void*)*3, x_59);
x_127 = lean_array_push(x_125, x_126);
lean_ctor_set(x_122, 1, x_127);
x_128 = lean_st_ref_set(x_3, x_122, x_123);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
lean_dec(x_130);
x_131 = lean_box(0);
lean_ctor_set(x_128, 0, x_131);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_135 = lean_ctor_get(x_122, 0);
x_136 = lean_ctor_get(x_122, 1);
x_137 = lean_ctor_get(x_122, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_122);
x_138 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_138, 0, x_53);
lean_ctor_set(x_138, 1, x_54);
lean_ctor_set(x_138, 2, x_55);
lean_ctor_set_uint8(x_138, sizeof(void*)*3, x_59);
x_139 = lean_array_push(x_136, x_138);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_137);
x_141 = lean_st_ref_set(x_3, x_140, x_123);
lean_dec(x_3);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_free_object(x_46);
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_60);
if (x_146 == 0)
{
return x_60;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_60, 0);
x_148 = lean_ctor_get(x_60, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_60);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; 
x_150 = lean_ctor_get(x_46, 0);
lean_inc(x_150);
lean_dec(x_46);
x_151 = lean_ctor_get(x_45, 1);
lean_inc(x_151);
lean_dec(x_45);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 3);
lean_inc(x_155);
x_156 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_157 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_158 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_154);
x_159 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_156, x_157, x_154, x_158, x_2, x_3, x_4, x_5, x_6, x_7, x_151);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_2, 1);
lean_inc(x_162);
lean_inc(x_152);
x_163 = lean_apply_1(x_162, x_152);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_inc(x_3);
x_165 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_161);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_st_ref_take(x_3, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 2);
lean_inc(x_172);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 x_173 = x_168;
} else {
 lean_dec_ref(x_168);
 x_173 = lean_box(0);
}
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_150);
x_175 = lean_array_push(x_172, x_174);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_170);
lean_ctor_set(x_176, 1, x_171);
lean_ctor_set(x_176, 2, x_175);
x_177 = lean_st_ref_set(x_3, x_176, x_169);
lean_dec(x_3);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_150);
lean_dec(x_3);
x_182 = lean_ctor_get(x_165, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_165, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_184 = x_165;
} else {
 lean_dec_ref(x_165);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_155);
lean_dec(x_150);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_186 = lean_st_ref_take(x_3, x_161);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 2);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_193, 0, x_152);
lean_ctor_set(x_193, 1, x_153);
lean_ctor_set(x_193, 2, x_154);
lean_ctor_set_uint8(x_193, sizeof(void*)*3, x_158);
x_194 = lean_array_push(x_190, x_193);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 3, 0);
} else {
 x_195 = x_192;
}
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_191);
x_196 = lean_st_ref_set(x_3, x_195, x_188);
lean_dec(x_3);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_155);
lean_dec(x_150);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_201 = lean_ctor_get(x_159, 1);
lean_inc(x_201);
lean_dec(x_159);
x_202 = lean_st_ref_take(x_3, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 2);
lean_inc(x_207);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 x_208 = x_203;
} else {
 lean_dec_ref(x_203);
 x_208 = lean_box(0);
}
x_209 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_209, 0, x_152);
lean_ctor_set(x_209, 1, x_153);
lean_ctor_set(x_209, 2, x_154);
lean_ctor_set_uint8(x_209, sizeof(void*)*3, x_158);
x_210 = lean_array_push(x_206, x_209);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_207);
x_212 = lean_st_ref_set(x_3, x_211, x_204);
lean_dec(x_3);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = lean_box(0);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_ctor_get(x_159, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_159, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_219 = x_159;
} else {
 lean_dec_ref(x_159);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
lean_dec(x_1);
x_221 = lean_ctor_get(x_42, 1);
lean_inc(x_221);
lean_dec(x_42);
x_222 = lean_ctor_get(x_43, 0);
lean_inc(x_222);
lean_dec(x_43);
x_223 = lean_ctor_get(x_222, 2);
lean_inc(x_223);
x_224 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_225 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_226 = 0;
lean_inc(x_3);
x_227 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_224, x_225, x_223, x_226, x_2, x_3, x_4, x_5, x_6, x_7, x_221);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_st_ref_take(x_3, x_228);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = !lean_is_exclusive(x_230);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_230, 1);
x_234 = lean_array_push(x_233, x_222);
lean_ctor_set(x_230, 1, x_234);
x_235 = lean_st_ref_set(x_3, x_230, x_231);
lean_dec(x_3);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_235, 0);
lean_dec(x_237);
x_238 = lean_box(0);
lean_ctor_set(x_235, 0, x_238);
return x_235;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
lean_dec(x_235);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = lean_ctor_get(x_230, 0);
x_243 = lean_ctor_get(x_230, 1);
x_244 = lean_ctor_get(x_230, 2);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_230);
x_245 = lean_array_push(x_243, x_222);
x_246 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_244);
x_247 = lean_st_ref_set(x_3, x_246, x_231);
lean_dec(x_3);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
else
{
uint8_t x_252; 
lean_dec(x_222);
lean_dec(x_3);
x_252 = !lean_is_exclusive(x_227);
if (x_252 == 0)
{
return x_227;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_227, 0);
x_254 = lean_ctor_get(x_227, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_227);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_1);
x_256 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_256 == 0)
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_40);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_258 = lean_ctor_get(x_40, 0);
x_259 = lean_ctor_get(x_39, 1);
lean_inc(x_259);
lean_dec(x_39);
x_260 = lean_ctor_get(x_2, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_258, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_258, 3);
lean_inc(x_263);
lean_inc(x_261);
x_264 = lean_apply_1(x_260, x_261);
x_265 = lean_unbox(x_264);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_inc(x_3);
lean_inc(x_258);
x_266 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_258, x_2, x_3, x_4, x_5, x_6, x_7, x_259);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_st_ref_take(x_3, x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_272 = lean_ctor_get(x_269, 2);
x_273 = lean_array_push(x_272, x_40);
lean_ctor_set(x_269, 2, x_273);
x_274 = lean_st_ref_set(x_3, x_269, x_270);
lean_dec(x_3);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_274, 0);
lean_dec(x_276);
x_277 = lean_box(0);
lean_ctor_set(x_274, 0, x_277);
return x_274;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec(x_274);
x_279 = lean_box(0);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_281 = lean_ctor_get(x_269, 0);
x_282 = lean_ctor_get(x_269, 1);
x_283 = lean_ctor_get(x_269, 2);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_269);
x_284 = lean_array_push(x_283, x_40);
x_285 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_282);
lean_ctor_set(x_285, 2, x_284);
x_286 = lean_st_ref_set(x_3, x_285, x_270);
lean_dec(x_3);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_288 = x_286;
} else {
 lean_dec_ref(x_286);
 x_288 = lean_box(0);
}
x_289 = lean_box(0);
if (lean_is_scalar(x_288)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_288;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_287);
return x_290;
}
}
else
{
uint8_t x_291; 
lean_free_object(x_40);
lean_dec(x_258);
lean_dec(x_3);
x_291 = !lean_is_exclusive(x_266);
if (x_291 == 0)
{
return x_266;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_266, 0);
x_293 = lean_ctor_get(x_266, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_266);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
lean_free_object(x_40);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_295 = lean_st_ref_take(x_3, x_259);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = !lean_is_exclusive(x_296);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_296, 1);
x_300 = 0;
x_301 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_301, 0, x_261);
lean_ctor_set(x_301, 1, x_262);
lean_ctor_set(x_301, 2, x_263);
lean_ctor_set_uint8(x_301, sizeof(void*)*3, x_300);
x_302 = lean_array_push(x_299, x_301);
lean_ctor_set(x_296, 1, x_302);
x_303 = lean_st_ref_set(x_3, x_296, x_297);
lean_dec(x_3);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_303, 0);
lean_dec(x_305);
x_306 = lean_box(0);
lean_ctor_set(x_303, 0, x_306);
return x_303;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_303, 1);
lean_inc(x_307);
lean_dec(x_303);
x_308 = lean_box(0);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_310 = lean_ctor_get(x_296, 0);
x_311 = lean_ctor_get(x_296, 1);
x_312 = lean_ctor_get(x_296, 2);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_296);
x_313 = 0;
x_314 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_314, 0, x_261);
lean_ctor_set(x_314, 1, x_262);
lean_ctor_set(x_314, 2, x_263);
lean_ctor_set_uint8(x_314, sizeof(void*)*3, x_313);
x_315 = lean_array_push(x_311, x_314);
x_316 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_316, 2, x_312);
x_317 = lean_st_ref_set(x_3, x_316, x_297);
lean_dec(x_3);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = lean_box(0);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_319;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_318);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_322 = lean_ctor_get(x_40, 0);
lean_inc(x_322);
lean_dec(x_40);
x_323 = lean_ctor_get(x_39, 1);
lean_inc(x_323);
lean_dec(x_39);
x_324 = lean_ctor_get(x_2, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_322, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 3);
lean_inc(x_327);
lean_inc(x_325);
x_328 = lean_apply_1(x_324, x_325);
x_329 = lean_unbox(x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_inc(x_3);
lean_inc(x_322);
x_330 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_322, x_2, x_3, x_4, x_5, x_6, x_7, x_323);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_st_ref_take(x_3, x_331);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_333, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 x_338 = x_333;
} else {
 lean_dec_ref(x_333);
 x_338 = lean_box(0);
}
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_322);
x_340 = lean_array_push(x_337, x_339);
if (lean_is_scalar(x_338)) {
 x_341 = lean_alloc_ctor(0, 3, 0);
} else {
 x_341 = x_338;
}
lean_ctor_set(x_341, 0, x_335);
lean_ctor_set(x_341, 1, x_336);
lean_ctor_set(x_341, 2, x_340);
x_342 = lean_st_ref_set(x_3, x_341, x_334);
lean_dec(x_3);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
x_345 = lean_box(0);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_343);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_322);
lean_dec(x_3);
x_347 = lean_ctor_get(x_330, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_330, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_349 = x_330;
} else {
 lean_dec_ref(x_330);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_322);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_351 = lean_st_ref_take(x_3, x_323);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 2);
lean_inc(x_356);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 x_357 = x_352;
} else {
 lean_dec_ref(x_352);
 x_357 = lean_box(0);
}
x_358 = 0;
x_359 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_359, 0, x_325);
lean_ctor_set(x_359, 1, x_326);
lean_ctor_set(x_359, 2, x_327);
lean_ctor_set_uint8(x_359, sizeof(void*)*3, x_358);
x_360 = lean_array_push(x_355, x_359);
if (lean_is_scalar(x_357)) {
 x_361 = lean_alloc_ctor(0, 3, 0);
} else {
 x_361 = x_357;
}
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set(x_361, 2, x_356);
x_362 = lean_st_ref_set(x_3, x_361, x_353);
lean_dec(x_3);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
x_365 = lean_box(0);
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_364;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_363);
return x_366;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_367 = lean_ctor_get(x_39, 1);
lean_inc(x_367);
lean_dec(x_39);
x_368 = lean_ctor_get(x_40, 0);
lean_inc(x_368);
lean_dec(x_40);
x_369 = lean_st_ref_take(x_3, x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = !lean_is_exclusive(x_370);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_373 = lean_ctor_get(x_370, 1);
x_374 = lean_ctor_get(x_368, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_368, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_368, 3);
lean_inc(x_376);
lean_dec(x_368);
x_377 = 0;
x_378 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_378, 0, x_374);
lean_ctor_set(x_378, 1, x_375);
lean_ctor_set(x_378, 2, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*3, x_377);
x_379 = lean_array_push(x_373, x_378);
lean_ctor_set(x_370, 1, x_379);
x_380 = lean_st_ref_set(x_3, x_370, x_371);
lean_dec(x_3);
x_381 = !lean_is_exclusive(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_380, 0);
lean_dec(x_382);
x_383 = lean_box(0);
lean_ctor_set(x_380, 0, x_383);
return x_380;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_380, 1);
lean_inc(x_384);
lean_dec(x_380);
x_385 = lean_box(0);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_387 = lean_ctor_get(x_370, 0);
x_388 = lean_ctor_get(x_370, 1);
x_389 = lean_ctor_get(x_370, 2);
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_370);
x_390 = lean_ctor_get(x_368, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_368, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_368, 3);
lean_inc(x_392);
lean_dec(x_368);
x_393 = 0;
x_394 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_391);
lean_ctor_set(x_394, 2, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*3, x_393);
x_395 = lean_array_push(x_388, x_394);
x_396 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_396, 0, x_387);
lean_ctor_set(x_396, 1, x_395);
lean_ctor_set(x_396, 2, x_389);
x_397 = lean_st_ref_set(x_3, x_396, x_371);
lean_dec(x_3);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
x_400 = lean_box(0);
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_398);
return x_401;
}
}
}
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_402 = lean_ctor_get(x_31, 1);
lean_inc(x_402);
lean_dec(x_31);
x_403 = lean_ctor_get(x_2, 0);
lean_inc(x_403);
lean_inc(x_1);
x_404 = lean_apply_1(x_403, x_1);
x_405 = lean_unbox(x_404);
lean_dec(x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_406 = lean_box(0);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_402);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; 
x_408 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_402);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_413);
lean_dec(x_1);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_418 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_417, x_2, x_3, x_4, x_5, x_6, x_7, x_416);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; 
x_419 = lean_ctor_get(x_415, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_414, 1);
lean_inc(x_421);
lean_dec(x_414);
x_422 = lean_ctor_get(x_419, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_419, 2);
lean_inc(x_424);
x_425 = lean_ctor_get(x_419, 3);
lean_inc(x_425);
x_426 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_427 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_428 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_424);
x_429 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_426, x_427, x_424, x_428, x_2, x_3, x_4, x_5, x_6, x_7, x_421);
if (lean_obj_tag(x_429) == 0)
{
uint8_t x_430; 
x_430 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_ctor_get(x_2, 1);
lean_inc(x_432);
lean_inc(x_422);
x_433 = lean_apply_1(x_432, x_422);
x_434 = lean_unbox(x_433);
lean_dec(x_433);
if (x_434 == 0)
{
lean_object* x_435; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_inc(x_3);
x_435 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_425, x_2, x_3, x_4, x_5, x_6, x_7, x_431);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = lean_st_ref_take(x_3, x_436);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = lean_ctor_get(x_438, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
x_442 = lean_ctor_get(x_438, 2);
lean_inc(x_442);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 lean_ctor_release(x_438, 2);
 x_443 = x_438;
} else {
 lean_dec_ref(x_438);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_444 = lean_alloc_ctor(0, 1, 0);
} else {
 x_444 = x_420;
 lean_ctor_set_tag(x_444, 0);
}
lean_ctor_set(x_444, 0, x_419);
x_445 = lean_array_push(x_442, x_444);
if (lean_is_scalar(x_443)) {
 x_446 = lean_alloc_ctor(0, 3, 0);
} else {
 x_446 = x_443;
}
lean_ctor_set(x_446, 0, x_440);
lean_ctor_set(x_446, 1, x_441);
lean_ctor_set(x_446, 2, x_445);
x_447 = lean_st_ref_set(x_3, x_446, x_439);
lean_dec(x_3);
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_449 = x_447;
} else {
 lean_dec_ref(x_447);
 x_449 = lean_box(0);
}
x_450 = lean_box(0);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_448);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_3);
x_452 = lean_ctor_get(x_435, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_435, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_454 = x_435;
} else {
 lean_dec_ref(x_435);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 2, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_425);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_456 = lean_st_ref_take(x_3, x_431);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_457, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 lean_ctor_release(x_457, 2);
 x_462 = x_457;
} else {
 lean_dec_ref(x_457);
 x_462 = lean_box(0);
}
x_463 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_463, 0, x_422);
lean_ctor_set(x_463, 1, x_423);
lean_ctor_set(x_463, 2, x_424);
lean_ctor_set_uint8(x_463, sizeof(void*)*3, x_428);
x_464 = lean_array_push(x_460, x_463);
if (lean_is_scalar(x_462)) {
 x_465 = lean_alloc_ctor(0, 3, 0);
} else {
 x_465 = x_462;
}
lean_ctor_set(x_465, 0, x_459);
lean_ctor_set(x_465, 1, x_464);
lean_ctor_set(x_465, 2, x_461);
x_466 = lean_st_ref_set(x_3, x_465, x_458);
lean_dec(x_3);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
x_469 = lean_box(0);
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_467);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_425);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_471 = lean_ctor_get(x_429, 1);
lean_inc(x_471);
lean_dec(x_429);
x_472 = lean_st_ref_take(x_3, x_471);
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 2);
lean_inc(x_477);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 lean_ctor_release(x_473, 2);
 x_478 = x_473;
} else {
 lean_dec_ref(x_473);
 x_478 = lean_box(0);
}
x_479 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_479, 0, x_422);
lean_ctor_set(x_479, 1, x_423);
lean_ctor_set(x_479, 2, x_424);
lean_ctor_set_uint8(x_479, sizeof(void*)*3, x_428);
x_480 = lean_array_push(x_476, x_479);
if (lean_is_scalar(x_478)) {
 x_481 = lean_alloc_ctor(0, 3, 0);
} else {
 x_481 = x_478;
}
lean_ctor_set(x_481, 0, x_475);
lean_ctor_set(x_481, 1, x_480);
lean_ctor_set(x_481, 2, x_477);
x_482 = lean_st_ref_set(x_3, x_481, x_474);
lean_dec(x_3);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_484 = x_482;
} else {
 lean_dec_ref(x_482);
 x_484 = lean_box(0);
}
x_485 = lean_box(0);
if (lean_is_scalar(x_484)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_484;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_483);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_487 = lean_ctor_get(x_429, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_429, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 x_489 = x_429;
} else {
 lean_dec_ref(x_429);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; 
lean_dec(x_1);
x_491 = lean_ctor_get(x_411, 1);
lean_inc(x_491);
lean_dec(x_411);
x_492 = lean_ctor_get(x_412, 0);
lean_inc(x_492);
lean_dec(x_412);
x_493 = lean_ctor_get(x_492, 2);
lean_inc(x_493);
x_494 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_495 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_496 = 0;
lean_inc(x_3);
x_497 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_494, x_495, x_493, x_496, x_2, x_3, x_4, x_5, x_6, x_7, x_491);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_498 = lean_ctor_get(x_497, 1);
lean_inc(x_498);
lean_dec(x_497);
x_499 = lean_st_ref_take(x_3, x_498);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_502 = lean_ctor_get(x_500, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_500, 1);
lean_inc(x_503);
x_504 = lean_ctor_get(x_500, 2);
lean_inc(x_504);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 lean_ctor_release(x_500, 2);
 x_505 = x_500;
} else {
 lean_dec_ref(x_500);
 x_505 = lean_box(0);
}
x_506 = lean_array_push(x_503, x_492);
if (lean_is_scalar(x_505)) {
 x_507 = lean_alloc_ctor(0, 3, 0);
} else {
 x_507 = x_505;
}
lean_ctor_set(x_507, 0, x_502);
lean_ctor_set(x_507, 1, x_506);
lean_ctor_set(x_507, 2, x_504);
x_508 = lean_st_ref_set(x_3, x_507, x_501);
lean_dec(x_3);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_510 = x_508;
} else {
 lean_dec_ref(x_508);
 x_510 = lean_box(0);
}
x_511 = lean_box(0);
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_510;
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_509);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_492);
lean_dec(x_3);
x_513 = lean_ctor_get(x_497, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_497, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_515 = x_497;
} else {
 lean_dec_ref(x_497);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_1);
x_517 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
x_518 = lean_ctor_get(x_409, 0);
lean_inc(x_518);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_519 = x_409;
} else {
 lean_dec_ref(x_409);
 x_519 = lean_box(0);
}
x_520 = lean_ctor_get(x_408, 1);
lean_inc(x_520);
lean_dec(x_408);
x_521 = lean_ctor_get(x_2, 1);
lean_inc(x_521);
x_522 = lean_ctor_get(x_518, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_518, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_518, 3);
lean_inc(x_524);
lean_inc(x_522);
x_525 = lean_apply_1(x_521, x_522);
x_526 = lean_unbox(x_525);
lean_dec(x_525);
if (x_526 == 0)
{
lean_object* x_527; 
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_inc(x_3);
lean_inc(x_518);
x_527 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_518, x_2, x_3, x_4, x_5, x_6, x_7, x_520);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
lean_dec(x_527);
x_529 = lean_st_ref_take(x_3, x_528);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_ctor_get(x_530, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_530, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_530, 2);
lean_inc(x_534);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 lean_ctor_release(x_530, 2);
 x_535 = x_530;
} else {
 lean_dec_ref(x_530);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_519;
}
lean_ctor_set(x_536, 0, x_518);
x_537 = lean_array_push(x_534, x_536);
if (lean_is_scalar(x_535)) {
 x_538 = lean_alloc_ctor(0, 3, 0);
} else {
 x_538 = x_535;
}
lean_ctor_set(x_538, 0, x_532);
lean_ctor_set(x_538, 1, x_533);
lean_ctor_set(x_538, 2, x_537);
x_539 = lean_st_ref_set(x_3, x_538, x_531);
lean_dec(x_3);
x_540 = lean_ctor_get(x_539, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_541 = x_539;
} else {
 lean_dec_ref(x_539);
 x_541 = lean_box(0);
}
x_542 = lean_box(0);
if (lean_is_scalar(x_541)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_541;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_540);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_3);
x_544 = lean_ctor_get(x_527, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_527, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_546 = x_527;
} else {
 lean_dec_ref(x_527);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_548 = lean_st_ref_take(x_3, x_520);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
x_553 = lean_ctor_get(x_549, 2);
lean_inc(x_553);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 lean_ctor_release(x_549, 2);
 x_554 = x_549;
} else {
 lean_dec_ref(x_549);
 x_554 = lean_box(0);
}
x_555 = 0;
x_556 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_556, 0, x_522);
lean_ctor_set(x_556, 1, x_523);
lean_ctor_set(x_556, 2, x_524);
lean_ctor_set_uint8(x_556, sizeof(void*)*3, x_555);
x_557 = lean_array_push(x_552, x_556);
if (lean_is_scalar(x_554)) {
 x_558 = lean_alloc_ctor(0, 3, 0);
} else {
 x_558 = x_554;
}
lean_ctor_set(x_558, 0, x_551);
lean_ctor_set(x_558, 1, x_557);
lean_ctor_set(x_558, 2, x_553);
x_559 = lean_st_ref_set(x_3, x_558, x_550);
lean_dec(x_3);
x_560 = lean_ctor_get(x_559, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_561 = x_559;
} else {
 lean_dec_ref(x_559);
 x_561 = lean_box(0);
}
x_562 = lean_box(0);
if (lean_is_scalar(x_561)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_561;
}
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_560);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_564 = lean_ctor_get(x_408, 1);
lean_inc(x_564);
lean_dec(x_408);
x_565 = lean_ctor_get(x_409, 0);
lean_inc(x_565);
lean_dec(x_409);
x_566 = lean_st_ref_take(x_3, x_564);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_ctor_get(x_567, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_567, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_567, 2);
lean_inc(x_571);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 lean_ctor_release(x_567, 2);
 x_572 = x_567;
} else {
 lean_dec_ref(x_567);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_565, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_565, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_565, 3);
lean_inc(x_575);
lean_dec(x_565);
x_576 = 0;
x_577 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_577, 0, x_573);
lean_ctor_set(x_577, 1, x_574);
lean_ctor_set(x_577, 2, x_575);
lean_ctor_set_uint8(x_577, sizeof(void*)*3, x_576);
x_578 = lean_array_push(x_570, x_577);
if (lean_is_scalar(x_572)) {
 x_579 = lean_alloc_ctor(0, 3, 0);
} else {
 x_579 = x_572;
}
lean_ctor_set(x_579, 0, x_569);
lean_ctor_set(x_579, 1, x_578);
lean_ctor_set(x_579, 2, x_571);
x_580 = lean_st_ref_set(x_3, x_579, x_568);
lean_dec(x_3);
x_581 = lean_ctor_get(x_580, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_582 = x_580;
} else {
 lean_dec_ref(x_580);
 x_582 = lean_box(0);
}
x_583 = lean_box(0);
if (lean_is_scalar(x_582)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_582;
}
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_581);
return x_584;
}
}
}
}
}
else
{
lean_object* x_585; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_585 = lean_box(0);
lean_ctor_set(x_9, 0, x_585);
return x_9;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; uint64_t x_589; uint64_t x_590; uint64_t x_591; uint64_t x_592; uint64_t x_593; uint64_t x_594; uint64_t x_595; size_t x_596; size_t x_597; size_t x_598; size_t x_599; size_t x_600; lean_object* x_601; uint8_t x_602; 
x_586 = lean_ctor_get(x_9, 1);
lean_inc(x_586);
lean_dec(x_9);
x_587 = lean_ctor_get(x_11, 1);
lean_inc(x_587);
lean_dec(x_11);
x_588 = lean_array_get_size(x_587);
x_589 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_590 = 32;
x_591 = lean_uint64_shift_right(x_589, x_590);
x_592 = lean_uint64_xor(x_589, x_591);
x_593 = 16;
x_594 = lean_uint64_shift_right(x_592, x_593);
x_595 = lean_uint64_xor(x_592, x_594);
x_596 = lean_uint64_to_usize(x_595);
x_597 = lean_usize_of_nat(x_588);
lean_dec(x_588);
x_598 = 1;
x_599 = lean_usize_sub(x_597, x_598);
x_600 = lean_usize_land(x_596, x_599);
x_601 = lean_array_uget(x_587, x_600);
lean_dec(x_587);
x_602 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___spec__1(x_1, x_601);
lean_dec(x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
lean_inc(x_1);
x_603 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_586);
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_605 = x_603;
} else {
 lean_dec_ref(x_603);
 x_605 = lean_box(0);
}
x_606 = lean_ctor_get(x_2, 0);
lean_inc(x_606);
lean_inc(x_1);
x_607 = lean_apply_1(x_606, x_1);
x_608 = lean_unbox(x_607);
lean_dec(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_609 = lean_box(0);
if (lean_is_scalar(x_605)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_605;
}
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_604);
return x_610;
}
else
{
lean_object* x_611; lean_object* x_612; 
lean_dec(x_605);
x_611 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_604);
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_613);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_616);
lean_dec(x_1);
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_621 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_620, x_2, x_3, x_4, x_5, x_6, x_7, x_619);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; 
x_622 = lean_ctor_get(x_618, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 x_623 = x_618;
} else {
 lean_dec_ref(x_618);
 x_623 = lean_box(0);
}
x_624 = lean_ctor_get(x_617, 1);
lean_inc(x_624);
lean_dec(x_617);
x_625 = lean_ctor_get(x_622, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_622, 1);
lean_inc(x_626);
x_627 = lean_ctor_get(x_622, 2);
lean_inc(x_627);
x_628 = lean_ctor_get(x_622, 3);
lean_inc(x_628);
x_629 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_630 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_631 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_627);
x_632 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_629, x_630, x_627, x_631, x_2, x_3, x_4, x_5, x_6, x_7, x_624);
if (lean_obj_tag(x_632) == 0)
{
uint8_t x_633; 
x_633 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_ctor_get(x_2, 1);
lean_inc(x_635);
lean_inc(x_625);
x_636 = lean_apply_1(x_635, x_625);
x_637 = lean_unbox(x_636);
lean_dec(x_636);
if (x_637 == 0)
{
lean_object* x_638; 
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
lean_inc(x_3);
x_638 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_628, x_2, x_3, x_4, x_5, x_6, x_7, x_634);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_639 = lean_ctor_get(x_638, 1);
lean_inc(x_639);
lean_dec(x_638);
x_640 = lean_st_ref_take(x_3, x_639);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_ctor_get(x_641, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_641, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_641, 2);
lean_inc(x_645);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 lean_ctor_release(x_641, 2);
 x_646 = x_641;
} else {
 lean_dec_ref(x_641);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_647 = lean_alloc_ctor(0, 1, 0);
} else {
 x_647 = x_623;
 lean_ctor_set_tag(x_647, 0);
}
lean_ctor_set(x_647, 0, x_622);
x_648 = lean_array_push(x_645, x_647);
if (lean_is_scalar(x_646)) {
 x_649 = lean_alloc_ctor(0, 3, 0);
} else {
 x_649 = x_646;
}
lean_ctor_set(x_649, 0, x_643);
lean_ctor_set(x_649, 1, x_644);
lean_ctor_set(x_649, 2, x_648);
x_650 = lean_st_ref_set(x_3, x_649, x_642);
lean_dec(x_3);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 x_652 = x_650;
} else {
 lean_dec_ref(x_650);
 x_652 = lean_box(0);
}
x_653 = lean_box(0);
if (lean_is_scalar(x_652)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_652;
}
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_651);
return x_654;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_3);
x_655 = lean_ctor_get(x_638, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_638, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_657 = x_638;
} else {
 lean_dec_ref(x_638);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(1, 2, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_655);
lean_ctor_set(x_658, 1, x_656);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_628);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_659 = lean_st_ref_take(x_3, x_634);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
lean_dec(x_659);
x_662 = lean_ctor_get(x_660, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_660, 1);
lean_inc(x_663);
x_664 = lean_ctor_get(x_660, 2);
lean_inc(x_664);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 lean_ctor_release(x_660, 2);
 x_665 = x_660;
} else {
 lean_dec_ref(x_660);
 x_665 = lean_box(0);
}
x_666 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_666, 0, x_625);
lean_ctor_set(x_666, 1, x_626);
lean_ctor_set(x_666, 2, x_627);
lean_ctor_set_uint8(x_666, sizeof(void*)*3, x_631);
x_667 = lean_array_push(x_663, x_666);
if (lean_is_scalar(x_665)) {
 x_668 = lean_alloc_ctor(0, 3, 0);
} else {
 x_668 = x_665;
}
lean_ctor_set(x_668, 0, x_662);
lean_ctor_set(x_668, 1, x_667);
lean_ctor_set(x_668, 2, x_664);
x_669 = lean_st_ref_set(x_3, x_668, x_661);
lean_dec(x_3);
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_671 = x_669;
} else {
 lean_dec_ref(x_669);
 x_671 = lean_box(0);
}
x_672 = lean_box(0);
if (lean_is_scalar(x_671)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_671;
}
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_670);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_628);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_674 = lean_ctor_get(x_632, 1);
lean_inc(x_674);
lean_dec(x_632);
x_675 = lean_st_ref_take(x_3, x_674);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = lean_ctor_get(x_676, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_676, 1);
lean_inc(x_679);
x_680 = lean_ctor_get(x_676, 2);
lean_inc(x_680);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 lean_ctor_release(x_676, 2);
 x_681 = x_676;
} else {
 lean_dec_ref(x_676);
 x_681 = lean_box(0);
}
x_682 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_682, 0, x_625);
lean_ctor_set(x_682, 1, x_626);
lean_ctor_set(x_682, 2, x_627);
lean_ctor_set_uint8(x_682, sizeof(void*)*3, x_631);
x_683 = lean_array_push(x_679, x_682);
if (lean_is_scalar(x_681)) {
 x_684 = lean_alloc_ctor(0, 3, 0);
} else {
 x_684 = x_681;
}
lean_ctor_set(x_684, 0, x_678);
lean_ctor_set(x_684, 1, x_683);
lean_ctor_set(x_684, 2, x_680);
x_685 = lean_st_ref_set(x_3, x_684, x_677);
lean_dec(x_3);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_687 = x_685;
} else {
 lean_dec_ref(x_685);
 x_687 = lean_box(0);
}
x_688 = lean_box(0);
if (lean_is_scalar(x_687)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_687;
}
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_686);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_690 = lean_ctor_get(x_632, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_632, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_692 = x_632;
} else {
 lean_dec_ref(x_632);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; lean_object* x_700; 
lean_dec(x_1);
x_694 = lean_ctor_get(x_614, 1);
lean_inc(x_694);
lean_dec(x_614);
x_695 = lean_ctor_get(x_615, 0);
lean_inc(x_695);
lean_dec(x_615);
x_696 = lean_ctor_get(x_695, 2);
lean_inc(x_696);
x_697 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_698 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_699 = 0;
lean_inc(x_3);
x_700 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_697, x_698, x_696, x_699, x_2, x_3, x_4, x_5, x_6, x_7, x_694);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_701 = lean_ctor_get(x_700, 1);
lean_inc(x_701);
lean_dec(x_700);
x_702 = lean_st_ref_take(x_3, x_701);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
lean_dec(x_702);
x_705 = lean_ctor_get(x_703, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_703, 1);
lean_inc(x_706);
x_707 = lean_ctor_get(x_703, 2);
lean_inc(x_707);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 lean_ctor_release(x_703, 2);
 x_708 = x_703;
} else {
 lean_dec_ref(x_703);
 x_708 = lean_box(0);
}
x_709 = lean_array_push(x_706, x_695);
if (lean_is_scalar(x_708)) {
 x_710 = lean_alloc_ctor(0, 3, 0);
} else {
 x_710 = x_708;
}
lean_ctor_set(x_710, 0, x_705);
lean_ctor_set(x_710, 1, x_709);
lean_ctor_set(x_710, 2, x_707);
x_711 = lean_st_ref_set(x_3, x_710, x_704);
lean_dec(x_3);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_713 = x_711;
} else {
 lean_dec_ref(x_711);
 x_713 = lean_box(0);
}
x_714 = lean_box(0);
if (lean_is_scalar(x_713)) {
 x_715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_715 = x_713;
}
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_712);
return x_715;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_695);
lean_dec(x_3);
x_716 = lean_ctor_get(x_700, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_700, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_718 = x_700;
} else {
 lean_dec_ref(x_700);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_716);
lean_ctor_set(x_719, 1, x_717);
return x_719;
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_1);
x_720 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_720 == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_721 = lean_ctor_get(x_612, 0);
lean_inc(x_721);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 x_722 = x_612;
} else {
 lean_dec_ref(x_612);
 x_722 = lean_box(0);
}
x_723 = lean_ctor_get(x_611, 1);
lean_inc(x_723);
lean_dec(x_611);
x_724 = lean_ctor_get(x_2, 1);
lean_inc(x_724);
x_725 = lean_ctor_get(x_721, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_721, 1);
lean_inc(x_726);
x_727 = lean_ctor_get(x_721, 3);
lean_inc(x_727);
lean_inc(x_725);
x_728 = lean_apply_1(x_724, x_725);
x_729 = lean_unbox(x_728);
lean_dec(x_728);
if (x_729 == 0)
{
lean_object* x_730; 
lean_dec(x_727);
lean_dec(x_726);
lean_dec(x_725);
lean_inc(x_3);
lean_inc(x_721);
x_730 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_721, x_2, x_3, x_4, x_5, x_6, x_7, x_723);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
lean_dec(x_730);
x_732 = lean_st_ref_take(x_3, x_731);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = lean_ctor_get(x_733, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_733, 1);
lean_inc(x_736);
x_737 = lean_ctor_get(x_733, 2);
lean_inc(x_737);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 lean_ctor_release(x_733, 2);
 x_738 = x_733;
} else {
 lean_dec_ref(x_733);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_739 = lean_alloc_ctor(1, 1, 0);
} else {
 x_739 = x_722;
}
lean_ctor_set(x_739, 0, x_721);
x_740 = lean_array_push(x_737, x_739);
if (lean_is_scalar(x_738)) {
 x_741 = lean_alloc_ctor(0, 3, 0);
} else {
 x_741 = x_738;
}
lean_ctor_set(x_741, 0, x_735);
lean_ctor_set(x_741, 1, x_736);
lean_ctor_set(x_741, 2, x_740);
x_742 = lean_st_ref_set(x_3, x_741, x_734);
lean_dec(x_3);
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_744 = x_742;
} else {
 lean_dec_ref(x_742);
 x_744 = lean_box(0);
}
x_745 = lean_box(0);
if (lean_is_scalar(x_744)) {
 x_746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_746 = x_744;
}
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_743);
return x_746;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_722);
lean_dec(x_721);
lean_dec(x_3);
x_747 = lean_ctor_get(x_730, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_730, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_749 = x_730;
} else {
 lean_dec_ref(x_730);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_747);
lean_ctor_set(x_750, 1, x_748);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_722);
lean_dec(x_721);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_751 = lean_st_ref_take(x_3, x_723);
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec(x_751);
x_754 = lean_ctor_get(x_752, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
x_756 = lean_ctor_get(x_752, 2);
lean_inc(x_756);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 lean_ctor_release(x_752, 2);
 x_757 = x_752;
} else {
 lean_dec_ref(x_752);
 x_757 = lean_box(0);
}
x_758 = 0;
x_759 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_759, 0, x_725);
lean_ctor_set(x_759, 1, x_726);
lean_ctor_set(x_759, 2, x_727);
lean_ctor_set_uint8(x_759, sizeof(void*)*3, x_758);
x_760 = lean_array_push(x_755, x_759);
if (lean_is_scalar(x_757)) {
 x_761 = lean_alloc_ctor(0, 3, 0);
} else {
 x_761 = x_757;
}
lean_ctor_set(x_761, 0, x_754);
lean_ctor_set(x_761, 1, x_760);
lean_ctor_set(x_761, 2, x_756);
x_762 = lean_st_ref_set(x_3, x_761, x_753);
lean_dec(x_3);
x_763 = lean_ctor_get(x_762, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_762)) {
 lean_ctor_release(x_762, 0);
 lean_ctor_release(x_762, 1);
 x_764 = x_762;
} else {
 lean_dec_ref(x_762);
 x_764 = lean_box(0);
}
x_765 = lean_box(0);
if (lean_is_scalar(x_764)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_764;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_763);
return x_766;
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; uint8_t x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_767 = lean_ctor_get(x_611, 1);
lean_inc(x_767);
lean_dec(x_611);
x_768 = lean_ctor_get(x_612, 0);
lean_inc(x_768);
lean_dec(x_612);
x_769 = lean_st_ref_take(x_3, x_767);
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
lean_dec(x_769);
x_772 = lean_ctor_get(x_770, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_770, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_770, 2);
lean_inc(x_774);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 lean_ctor_release(x_770, 2);
 x_775 = x_770;
} else {
 lean_dec_ref(x_770);
 x_775 = lean_box(0);
}
x_776 = lean_ctor_get(x_768, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_768, 1);
lean_inc(x_777);
x_778 = lean_ctor_get(x_768, 3);
lean_inc(x_778);
lean_dec(x_768);
x_779 = 0;
x_780 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_780, 0, x_776);
lean_ctor_set(x_780, 1, x_777);
lean_ctor_set(x_780, 2, x_778);
lean_ctor_set_uint8(x_780, sizeof(void*)*3, x_779);
x_781 = lean_array_push(x_773, x_780);
if (lean_is_scalar(x_775)) {
 x_782 = lean_alloc_ctor(0, 3, 0);
} else {
 x_782 = x_775;
}
lean_ctor_set(x_782, 0, x_772);
lean_ctor_set(x_782, 1, x_781);
lean_ctor_set(x_782, 2, x_774);
x_783 = lean_st_ref_set(x_3, x_782, x_771);
lean_dec(x_3);
x_784 = lean_ctor_get(x_783, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_785 = x_783;
} else {
 lean_dec_ref(x_783);
 x_785 = lean_box(0);
}
x_786 = lean_box(0);
if (lean_is_scalar(x_785)) {
 x_787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_787 = x_785;
}
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_787, 1, x_784);
return x_787;
}
}
}
}
else
{
lean_object* x_788; lean_object* x_789; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_788 = lean_box(0);
x_789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_586);
return x_789;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_Closure_collectArg(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_11, x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_23;
}
}
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_array_get_size(x_25);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_26, 0, x_35);
return x_26;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_26);
x_36 = 0;
x_37 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_25, x_36, x_37, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_25);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_array_get_size(x_25);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_41, x_41);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_51 = lean_box(0);
x_52 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_25, x_49, x_50, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_25);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
return x_26;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_8);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_16 = 0;
x_17 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_14, x_15, x_13, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_12 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_10, x_11, x_9, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Compiler_LCNF_Closure_collectParams(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_20);
x_21 = l_Lean_Compiler_LCNF_Closure_collectCode(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = l_Lean_Compiler_LCNF_Closure_collectCode(x_18, x_25, x_3, x_4, x_5, x_6, x_7, x_17);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_Closure_collectParams(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Compiler_LCNF_Closure_collectCode(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Compiler_LCNF_Closure_collectCode(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 1;
x_37 = lean_usize_add(x_2, x_36);
x_2 = x_37;
x_4 = x_34;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_14 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_15 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_12, x_13, x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_9, 3);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_isForall(x_11);
lean_dec(x_11);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_18, x_22, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_1 = x_10;
x_8 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_9, 3);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_34);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_31, x_35, x_3, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_1 = x_10;
x_8 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 3:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 0);
lean_dec(x_49);
x_50 = lean_array_get_size(x_48);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_55);
return x_1;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_1);
x_56 = 0;
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = lean_box(0);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_48, x_56, x_57, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_48);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_61, x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = lean_box(0);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_60, x_69, x_70, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_60);
return x_72;
}
}
}
}
case 4:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_76 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_77 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_78 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_75, x_76, x_74, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get(x_73, 2);
lean_inc(x_80);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_81, 1);
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_73, 3);
lean_inc(x_85);
lean_dec(x_73);
x_86 = lean_array_get_size(x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_86);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_box(0);
lean_ctor_set(x_81, 0, x_89);
return x_81;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_86, x_86);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_box(0);
lean_ctor_set(x_81, 0, x_91);
return x_81;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_81);
x_92 = 0;
x_93 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_94 = lean_box(0);
x_95 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_85, x_92, x_93, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_85);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_ctor_get(x_73, 3);
lean_inc(x_97);
lean_dec(x_73);
x_98 = lean_array_get_size(x_97);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_nat_dec_lt(x_99, x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
else
{
uint8_t x_103; 
x_103 = lean_nat_dec_le(x_98, x_98);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_96);
return x_105;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_108 = lean_box(0);
x_109 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_97, x_106, x_107, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_96);
lean_dec(x_97);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_81);
if (x_110 == 0)
{
return x_81;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_81, 0);
x_112 = lean_ctor_get(x_81, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_81);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_78);
if (x_114 == 0)
{
return x_78;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_78, 0);
x_116 = lean_ctor_get(x_78, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_78);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 5:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
lean_dec(x_1);
x_119 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_119;
}
case 6:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_122 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_123 = 0;
x_124 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_121, x_122, x_120, x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_124;
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_127 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_125, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_1 = x_126;
x_8 = x_128;
goto _start;
}
else
{
uint8_t x_130; 
lean_dec(x_126);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_127);
if (x_130 == 0)
{
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_6, x_15, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_2, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_6, x_8);
x_4 = x_11;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__3;
x_2 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = 0;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__5;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = lean_apply_7(x_1, x_10, x_14, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = lean_array_size(x_25);
x_27 = 0;
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1(x_24, x_25, x_25, x_26, x_27, x_23, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_21, 2);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_array_get_size(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_35 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_17);
lean_ctor_set(x_28, 0, x_12);
return x_28;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_37 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
lean_ctor_set(x_19, 1, x_37);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_17);
lean_ctor_set(x_28, 0, x_12);
return x_28;
}
else
{
size_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_39 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(x_30, x_31, x_27, x_38, x_39);
lean_dec(x_31);
lean_dec(x_30);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_17);
lean_ctor_set(x_28, 0, x_12);
return x_28;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_ctor_get(x_21, 2);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
x_47 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
lean_ctor_set(x_19, 1, x_47);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_17);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_44, x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
x_50 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
lean_ctor_set(x_19, 1, x_50);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_17);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
else
{
size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_53 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(x_41, x_43, x_27, x_52, x_53);
lean_dec(x_43);
lean_dec(x_41);
lean_ctor_set(x_19, 1, x_54);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_17);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_12);
lean_ctor_set(x_55, 1, x_42);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_box(0);
x_59 = lean_box(0);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
x_61 = lean_array_size(x_60);
x_62 = 0;
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1(x_59, x_60, x_60, x_61, x_62, x_58, x_4, x_5, x_6, x_7, x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_56, 2);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_array_get_size(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_64);
x_71 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_12, 1, x_72);
lean_ctor_set(x_12, 0, x_17);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_68, x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_64);
x_75 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_12, 1, x_76);
lean_ctor_set(x_12, 0, x_17);
if (lean_is_scalar(x_66)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_66;
}
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_65);
return x_77;
}
else
{
size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_79 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_80 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(x_64, x_67, x_62, x_78, x_79);
lean_dec(x_67);
lean_dec(x_64);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_60);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_12, 1, x_81);
lean_ctor_set(x_12, 0, x_17);
if (lean_is_scalar(x_66)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_66;
}
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_82, 1, x_65);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_16);
if (x_83 == 0)
{
return x_16;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_16, 0);
x_85 = lean_ctor_get(x_16, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_16);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_12, 0);
x_88 = lean_ctor_get(x_12, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_87);
x_89 = lean_apply_7(x_1, x_10, x_87, x_4, x_5, x_6, x_7, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_get(x_87, x_91);
lean_dec(x_87);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
x_97 = lean_box(0);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
x_99 = lean_array_size(x_98);
x_100 = 0;
x_101 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1(x_97, x_98, x_98, x_99, x_100, x_96, x_4, x_5, x_6, x_7, x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_93, 2);
lean_inc(x_105);
lean_dec(x_93);
x_106 = lean_array_get_size(x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_lt(x_107, x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_102);
x_109 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
if (lean_is_scalar(x_95)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_95;
}
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_90);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_104;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
return x_112;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_106, x_106);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_102);
x_114 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
if (lean_is_scalar(x_95)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_95;
}
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_90);
lean_ctor_set(x_116, 1, x_115);
if (lean_is_scalar(x_104)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_104;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_103);
return x_117;
}
else
{
size_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_119 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4;
x_120 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(x_102, x_105, x_100, x_118, x_119);
lean_dec(x_105);
lean_dec(x_102);
if (lean_is_scalar(x_95)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_95;
}
lean_ctor_set(x_121, 0, x_98);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_90);
lean_ctor_set(x_122, 1, x_121);
if (lean_is_scalar(x_104)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_104;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_103);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_124 = lean_ctor_get(x_89, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_89, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_126 = x_89;
} else {
 lean_dec_ref(x_89);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_run___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Closure_run___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_run___spec__2___at_Lean_Compiler_LCNF_Closure_run___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Closure_collectType___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectType___closed__1);
l_Lean_Compiler_LCNF_Closure_collectType___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectType___closed__2);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__3 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__3);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__4);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__5 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
