// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: Lean.Expr Lean.Util.PtrSet Lean.Declaration
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
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4;
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__5;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6;
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Expr_getUsedConstants___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_50 = lean_ctor_get(x_13, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
x_52 = lean_array_get_size(x_51);
x_53 = lean_ptr_addr(x_2);
x_54 = lean_usize_to_uint64(x_53);
x_55 = 11;
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_57 = 32;
x_58 = lean_uint64_shift_right(x_56, x_57);
x_59 = lean_uint64_xor(x_56, x_58);
x_60 = 16;
x_61 = lean_uint64_shift_right(x_59, x_60);
x_62 = lean_uint64_xor(x_59, x_61);
x_63 = lean_uint64_to_usize(x_62);
x_64 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_65 = 1;
x_66 = lean_usize_sub(x_64, x_65);
x_67 = lean_usize_land(x_63, x_66);
x_68 = lean_array_uget(x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_2, x_68);
if (x_69 == 0)
{
lean_dec(x_4);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_13);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_71 = lean_ctor_get(x_13, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_13, 0);
lean_dec(x_72);
x_73 = lean_box(0);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_50, x_74);
lean_dec(x_50);
lean_inc(x_2);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_68);
x_77 = lean_array_uset(x_51, x_67, x_76);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_nat_mul(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(x_77);
lean_ctor_set(x_13, 1, x_84);
lean_ctor_set(x_13, 0, x_75);
x_15 = x_13;
goto block_49;
}
else
{
lean_ctor_set(x_13, 1, x_77);
lean_ctor_set(x_13, 0, x_75);
x_15 = x_13;
goto block_49;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_13);
x_85 = lean_box(0);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_50, x_86);
lean_dec(x_50);
lean_inc(x_2);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_2);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_68);
x_89 = lean_array_uset(x_51, x_67, x_88);
x_90 = lean_unsigned_to_nat(4u);
x_91 = lean_nat_mul(x_87, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = lean_nat_div(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_le(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_15 = x_97;
goto block_49;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
x_15 = x_98;
goto block_49;
}
}
}
else
{
lean_dec(x_68);
lean_dec(x_51);
lean_dec(x_50);
x_15 = x_13;
goto block_49;
}
}
else
{
lean_object* x_99; 
lean_dec(x_68);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_4);
return x_99;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_5, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_2 = x_6;
x_3 = x_9;
x_4 = x_10;
goto _start;
}
block_49:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_NameHashSet_contains(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_NameHashSet_insert(x_14, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_2(x_1, x_17, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
case 5:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_14);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_26 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_24, x_3, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_2 = x_25;
x_3 = x_27;
x_4 = x_28;
goto _start;
}
case 6:
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
lean_dec(x_14);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
x_5 = x_30;
x_6 = x_31;
x_7 = x_16;
goto block_12;
}
case 7:
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_14);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
lean_dec(x_2);
x_5 = x_32;
x_6 = x_33;
x_7 = x_16;
goto block_12;
}
case 8:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
lean_dec(x_14);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_dec(x_2);
lean_inc(x_1);
x_37 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_34, x_3, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_1);
x_40 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_35, x_38, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_2 = x_36;
x_3 = x_41;
x_4 = x_42;
goto _start;
}
case 10:
{
lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_14);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_2 = x_44;
x_4 = x_16;
goto _start;
}
case 11:
{
lean_object* x_46; 
lean_dec(x_15);
lean_dec(x_14);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
lean_dec(x_2);
x_2 = x_46;
x_4 = x_16;
goto _start;
}
default: 
{
lean_object* x_48; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_16);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrSet___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__5;
x_2 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6;
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_3, x_1, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6;
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_4, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstants___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstants___lam__0), 2, 0);
x_3 = l_Lean_Expr_getUsedConstants___closed__0;
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6;
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_NameSet_insert(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstantsAsSet___lam__0), 2, 0);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6;
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_5, x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_ConstantInfo_type(x_1);
x_3 = l_Lean_Expr_getUsedConstantsAsSet(x_2);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
lean_inc(x_1);
x_6 = l_Lean_ConstantInfo_value_x3f(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_getUsedConstantsAsSet(x_8);
x_10 = l_Lean_NameSet_append(x_3, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(x_12);
x_14 = l_Lean_NameSet_append(x_3, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = l_Lean_NameSet_insert(x_18, x_17);
x_20 = l_Lean_NameSet_append(x_3, x_19);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(x_22);
x_24 = l_Lean_NameSet_append(x_3, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = l_Lean_NameSet_append(x_3, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_Expr_getUsedConstantsAsSet(x_27);
x_29 = l_Lean_NameSet_append(x_3, x_28);
return x_29;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__5 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__5();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__5);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__6);
l_Lean_Expr_getUsedConstants___closed__0 = _init_l_Lean_Expr_getUsedConstants___closed__0();
lean_mark_persistent(l_Lean_Expr_getUsedConstants___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
