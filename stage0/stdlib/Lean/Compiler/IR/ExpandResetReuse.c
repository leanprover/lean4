// Lean compiler output
// Module: Lean.Compiler.IR.ExpandResetReuse
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds Lean.Compiler.IR.FreeVars
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l_Lean_IR_instHashableVarId___lam__0___boxed(lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_IR_instBEqVarId___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instBEqVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__0;
x_5 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
switch (lean_obj_tag(x_2)) {
case 3:
{
goto block_74;
}
case 4:
{
goto block_74;
}
case 5:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_ctor_get(x_3, 1);
x_78 = lean_array_get_size(x_77);
x_79 = lean_uint64_of_nat(x_1);
x_80 = 32;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = 16;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_88 = 1;
x_89 = lean_usize_sub(x_87, x_88);
x_90 = lean_usize_land(x_86, x_89);
x_91 = lean_array_uget(x_77, x_90);
lean_inc(x_91);
lean_inc(x_1);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_4, x_1, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_76, x_93);
lean_dec(x_76);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_2);
lean_ctor_set(x_95, 2, x_91);
x_96 = lean_array_uset(x_77, x_90, x_95);
x_97 = lean_unsigned_to_nat(4u);
x_98 = lean_nat_mul(x_94, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_nat_div(x_98, x_99);
lean_dec(x_98);
x_101 = lean_array_get_size(x_96);
x_102 = lean_nat_dec_le(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_96);
lean_ctor_set(x_3, 1, x_103);
lean_ctor_set(x_3, 0, x_94);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_96);
lean_ctor_set(x_3, 0, x_94);
return x_3;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_box(0);
x_105 = lean_array_uset(x_77, x_90, x_104);
x_106 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_91);
x_107 = lean_array_uset(x_105, x_90, x_106);
lean_ctor_set(x_3, 1, x_107);
return x_3;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_108 = lean_ctor_get(x_3, 0);
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_3);
x_110 = lean_array_get_size(x_109);
x_111 = lean_uint64_of_nat(x_1);
x_112 = 32;
x_113 = lean_uint64_shift_right(x_111, x_112);
x_114 = lean_uint64_xor(x_111, x_113);
x_115 = 16;
x_116 = lean_uint64_shift_right(x_114, x_115);
x_117 = lean_uint64_xor(x_114, x_116);
x_118 = lean_uint64_to_usize(x_117);
x_119 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_120 = 1;
x_121 = lean_usize_sub(x_119, x_120);
x_122 = lean_usize_land(x_118, x_121);
x_123 = lean_array_uget(x_109, x_122);
lean_inc(x_123);
lean_inc(x_1);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_4, x_1, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_108, x_125);
lean_dec(x_108);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 2, x_123);
x_128 = lean_array_uset(x_109, x_122, x_127);
x_129 = lean_unsigned_to_nat(4u);
x_130 = lean_nat_mul(x_126, x_129);
x_131 = lean_unsigned_to_nat(3u);
x_132 = lean_nat_div(x_130, x_131);
lean_dec(x_130);
x_133 = lean_array_get_size(x_128);
x_134 = lean_nat_dec_le(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_128);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_126);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_128);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_box(0);
x_139 = lean_array_uset(x_109, x_122, x_138);
x_140 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_123);
x_141 = lean_array_uset(x_139, x_122, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_108);
lean_ctor_set(x_142, 1, x_141);
return x_142;
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
block_74:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_uint64_of_nat(x_1);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_8, x_21);
lean_inc(x_22);
lean_inc(x_1);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_4, x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_7, x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_22);
x_27 = lean_array_uset(x_8, x_21, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_27);
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_box(0);
x_36 = lean_array_uset(x_8, x_21, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_22);
x_38 = lean_array_uset(x_36, x_21, x_37);
lean_ctor_set(x_3, 1, x_38);
return x_3;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; uint8_t x_55; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_41 = lean_array_get_size(x_40);
x_42 = lean_uint64_of_nat(x_1);
x_43 = 32;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = 16;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = lean_uint64_to_usize(x_48);
x_50 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_51 = 1;
x_52 = lean_usize_sub(x_50, x_51);
x_53 = lean_usize_land(x_49, x_52);
x_54 = lean_array_uget(x_40, x_53);
lean_inc(x_54);
lean_inc(x_1);
x_55 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_4, x_1, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_39, x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set(x_58, 2, x_54);
x_59 = lean_array_uset(x_40, x_53, x_58);
x_60 = lean_unsigned_to_nat(4u);
x_61 = lean_nat_mul(x_57, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_nat_div(x_61, x_62);
lean_dec(x_61);
x_64 = lean_array_get_size(x_59);
x_65 = lean_nat_dec_le(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_box(0);
x_70 = lean_array_uset(x_40, x_53, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_54);
x_72 = lean_array_uset(x_70, x_53, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_39);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = lean_uint64_of_nat(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_12, x_4);
x_5 = x_13;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_14, x_4);
x_5 = x_15;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_5, x_2);
switch (lean_obj_tag(x_4)) {
case 3:
{
goto block_75;
}
case 4:
{
goto block_75;
}
case 5:
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_6);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; uint8_t x_93; 
x_77 = lean_ctor_get(x_6, 0);
x_78 = lean_ctor_get(x_6, 1);
x_79 = lean_array_get_size(x_78);
x_80 = lean_uint64_of_nat(x_3);
x_81 = 32;
x_82 = lean_uint64_shift_right(x_80, x_81);
x_83 = lean_uint64_xor(x_80, x_82);
x_84 = 16;
x_85 = lean_uint64_shift_right(x_83, x_84);
x_86 = lean_uint64_xor(x_83, x_85);
x_87 = lean_uint64_to_usize(x_86);
x_88 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_89 = 1;
x_90 = lean_usize_sub(x_88, x_89);
x_91 = lean_usize_land(x_87, x_90);
x_92 = lean_array_uget(x_78, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_77, x_94);
lean_dec(x_77);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_96, 1, x_4);
lean_ctor_set(x_96, 2, x_92);
x_97 = lean_array_uset(x_78, x_91, x_96);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_nat_mul(x_95, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_97);
lean_ctor_set(x_6, 1, x_104);
lean_ctor_set(x_6, 0, x_95);
return x_6;
}
else
{
lean_ctor_set(x_6, 1, x_97);
lean_ctor_set(x_6, 0, x_95);
return x_6;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_box(0);
x_106 = lean_array_uset(x_78, x_91, x_105);
x_107 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_92);
x_108 = lean_array_uset(x_106, x_91, x_107);
lean_ctor_set(x_6, 1, x_108);
return x_6;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; size_t x_123; lean_object* x_124; uint8_t x_125; 
x_109 = lean_ctor_get(x_6, 0);
x_110 = lean_ctor_get(x_6, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_6);
x_111 = lean_array_get_size(x_110);
x_112 = lean_uint64_of_nat(x_3);
x_113 = 32;
x_114 = lean_uint64_shift_right(x_112, x_113);
x_115 = lean_uint64_xor(x_112, x_114);
x_116 = 16;
x_117 = lean_uint64_shift_right(x_115, x_116);
x_118 = lean_uint64_xor(x_115, x_117);
x_119 = lean_uint64_to_usize(x_118);
x_120 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_121 = 1;
x_122 = lean_usize_sub(x_120, x_121);
x_123 = lean_usize_land(x_119, x_122);
x_124 = lean_array_uget(x_110, x_123);
x_125 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_add(x_109, x_126);
lean_dec(x_109);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_3);
lean_ctor_set(x_128, 1, x_4);
lean_ctor_set(x_128, 2, x_124);
x_129 = lean_array_uset(x_110, x_123, x_128);
x_130 = lean_unsigned_to_nat(4u);
x_131 = lean_nat_mul(x_127, x_130);
x_132 = lean_unsigned_to_nat(3u);
x_133 = lean_nat_div(x_131, x_132);
lean_dec(x_131);
x_134 = lean_array_get_size(x_129);
x_135 = lean_nat_dec_le(x_133, x_134);
lean_dec(x_134);
lean_dec(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_129);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_129);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_box(0);
x_140 = lean_array_uset(x_110, x_123, x_139);
x_141 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_124);
x_142 = lean_array_uset(x_140, x_123, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_109);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
block_75:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_uint64_of_nat(x_3);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_23);
x_28 = lean_array_uset(x_9, x_22, x_27);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_26, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_28);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
else
{
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_box(0);
x_37 = lean_array_uset(x_9, x_22, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_23);
x_39 = lean_array_uset(x_37, x_22, x_38);
lean_ctor_set(x_6, 1, x_39);
return x_6;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_40 = lean_ctor_get(x_6, 0);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_42 = lean_array_get_size(x_41);
x_43 = lean_uint64_of_nat(x_3);
x_44 = 32;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = 16;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = 1;
x_53 = lean_usize_sub(x_51, x_52);
x_54 = lean_usize_land(x_50, x_53);
x_55 = lean_array_uget(x_41, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_40, x_57);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_array_uset(x_41, x_54, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_41, x_54, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_55);
x_73 = lean_array_uset(x_71, x_54, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_40);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
case 1:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_1, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 3);
lean_inc(x_145);
lean_dec(x_1);
x_146 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_145, x_2);
x_1 = x_144;
x_2 = x_146;
goto _start;
}
case 10:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_1, 3);
lean_inc(x_148);
lean_dec(x_1);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_array_get_size(x_148);
x_151 = lean_nat_dec_lt(x_149, x_150);
if (x_151 == 0)
{
lean_dec(x_150);
lean_dec(x_148);
return x_2;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_150, x_150);
if (x_152 == 0)
{
lean_dec(x_150);
lean_dec(x_148);
return x_2;
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; 
x_153 = 0;
x_154 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_155 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(x_148, x_153, x_154, x_2);
lean_dec(x_148);
return x_155;
}
}
}
default: 
{
uint8_t x_156; 
x_156 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_156 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_1, 3);
lean_inc(x_157);
lean_dec(x_1);
x_1 = x_157;
goto _start;
}
case 1:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_1, 3);
lean_inc(x_159);
lean_dec(x_1);
x_1 = x_159;
goto _start;
}
case 2:
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_1, 3);
lean_inc(x_161);
lean_dec(x_1);
x_1 = x_161;
goto _start;
}
case 3:
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_1, 2);
lean_inc(x_163);
lean_dec(x_1);
x_1 = x_163;
goto _start;
}
case 4:
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_1, 3);
lean_inc(x_165);
lean_dec(x_1);
x_1 = x_165;
goto _start;
}
case 5:
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_1, 5);
lean_inc(x_167);
lean_dec(x_1);
x_1 = x_167;
goto _start;
}
case 6:
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_1, 2);
lean_inc(x_169);
lean_dec(x_1);
x_1 = x_169;
goto _start;
}
case 7:
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_1, 2);
lean_inc(x_171);
lean_dec(x_1);
x_1 = x_171;
goto _start;
}
case 8:
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_1, 1);
lean_inc(x_173);
lean_dec(x_1);
x_1 = x_173;
goto _start;
}
case 9:
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_1, 1);
lean_inc(x_175);
lean_dec(x_1);
x_1 = x_175;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4;
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4;
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_14; 
x_6 = lean_box(1);
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_15);
lean_dec(x_15);
x_7 = x_16;
goto block_13;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_17);
lean_dec(x_17);
x_7 = x_18;
goto block_13;
}
block_13:
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
if (x_5 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_6);
return x_12;
}
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 3);
x_2 = x_8;
goto _start;
}
}
case 7:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_nat_dec_eq(x_1, x_10);
if (x_12 == 0)
{
x_2 = x_11;
goto _start;
}
else
{
return x_12;
}
}
case 10:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
return x_19;
}
else
{
if (x_17 == 0)
{
lean_dec(x_16);
return x_17;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(x_1, x_14, x_20, x_21);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
}
default: 
{
uint8_t x_25; 
x_25 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_25 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 3);
x_2 = x_26;
goto _start;
}
case 1:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 3);
x_2 = x_28;
goto _start;
}
case 2:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 3);
x_2 = x_30;
goto _start;
}
case 3:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
x_2 = x_32;
goto _start;
}
case 4:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_2, 3);
x_2 = x_34;
goto _start;
}
case 5:
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_2, 5);
x_2 = x_36;
goto _start;
}
case 6:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_2, 2);
x_2 = x_38;
goto _start;
}
case 7:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_2, 2);
x_2 = x_40;
goto _start;
}
case 8:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_2, 1);
x_2 = x_42;
goto _start;
}
case 9:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 1);
x_2 = x_44;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Array_reverse___redArg(x_1);
x_6 = l_Array_append___redArg(x_2, x_5);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_get_size(x_2);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(13);
x_20 = l_Array_back_x21___redArg(x_19, x_2);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 4:
{
lean_dec(x_21);
x_5 = x_20;
goto block_9;
}
case 5:
{
lean_dec(x_21);
x_5 = x_20;
goto block_9;
}
default: 
{
lean_dec(x_21);
lean_dec(x_20);
goto block_12;
}
}
}
case 6:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
x_25 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 1);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_26 = x_20;
} else {
 lean_dec_ref(x_20);
 x_26 = lean_box(0);
}
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_23, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_30 = lean_array_fget(x_2, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 3)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_51; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_51 = lean_nat_dec_eq(x_32, x_22);
lean_dec(x_32);
if (x_51 == 0)
{
lean_dec(x_34);
x_35 = x_51;
goto block_50;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_eq(x_1, x_34);
lean_dec(x_34);
x_35 = x_52;
goto block_50;
}
block_50:
{
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_36 = lean_box(0);
x_37 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_4, x_2, x_3, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_array_pop(x_2);
x_39 = lean_array_pop(x_38);
lean_inc(x_22);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_22);
x_41 = lean_array_set(x_3, x_33, x_40);
lean_dec(x_33);
x_42 = lean_array_push(x_4, x_30);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_eq(x_23, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_nat_sub(x_23, x_43);
lean_dec(x_23);
if (lean_is_scalar(x_26)) {
 x_46 = lean_alloc_ctor(6, 3, 2);
} else {
 x_46 = x_26;
}
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_24);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_25);
x_47 = lean_array_push(x_42, x_46);
x_2 = x_39;
x_3 = x_41;
x_4 = x_47;
goto _start;
}
else
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_2 = x_39;
x_3 = x_41;
x_4 = x_42;
goto _start;
}
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
goto block_15;
}
}
else
{
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
goto block_15;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_16);
x_53 = lean_box(0);
x_54 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_4, x_2, x_3, x_53);
return x_54;
}
}
default: 
{
lean_dec(x_20);
lean_dec(x_16);
goto block_12;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
x_55 = lean_box(0);
x_56 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_4, x_2, x_3, x_55);
return x_56;
}
block_9:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_pop(x_2);
x_7 = lean_array_push(x_4, x_5);
x_2 = x_6;
x_4 = x_7;
goto _start;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_4, x_2, x_3, x_10);
return x_11;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_4, x_2, x_3, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_mk_array(x_1, x_4);
x_6 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
x_7 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_16);
lean_ctor_set(x_6, 1, x_17);
x_9 = x_6;
goto block_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_9 = x_21;
goto block_14;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_23);
lean_ctor_set(x_6, 0, x_24);
x_9 = x_6;
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_9 = x_27;
goto block_14;
}
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_1, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
x_17 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_11);
lean_ctor_set(x_2, 3, x_17);
return x_2;
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_1, x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
x_26 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_21);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_9);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 3);
x_32 = lean_ctor_get(x_2, 2);
lean_dec(x_32);
x_33 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_31);
lean_ctor_set(x_2, 3, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_37 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_9);
lean_ctor_set(x_38, 3, x_37);
return x_38;
}
}
}
case 7:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_nat_dec_eq(x_1, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_42);
lean_ctor_set(x_2, 2, x_44);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_41);
lean_dec(x_40);
return x_42;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_50 = lean_nat_dec_eq(x_1, x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_49);
x_52 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 1, x_48);
return x_52;
}
else
{
lean_dec(x_46);
lean_dec(x_45);
return x_49;
}
}
}
case 10:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_2, 3);
x_55 = lean_array_size(x_54);
x_56 = 0;
x_57 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(x_1, x_55, x_56, x_54);
lean_ctor_set(x_2, 3, x_57);
return x_2;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
x_60 = lean_ctor_get(x_2, 2);
x_61 = lean_ctor_get(x_2, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_2);
x_62 = lean_array_size(x_61);
x_63 = 0;
x_64 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(x_1, x_62, x_63, x_61);
x_65 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_64);
return x_65;
}
}
default: 
{
uint8_t x_66; 
x_66 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_66 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_2, 3);
lean_inc(x_67);
x_3 = x_67;
goto block_8;
}
case 1:
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_2, 3);
lean_inc(x_68);
x_3 = x_68;
goto block_8;
}
case 2:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_2, 3);
lean_inc(x_69);
x_3 = x_69;
goto block_8;
}
case 3:
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_3 = x_70;
goto block_8;
}
case 4:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
x_3 = x_71;
goto block_8;
}
case 5:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_2, 5);
lean_inc(x_72);
x_3 = x_72;
goto block_8;
}
case 6:
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_2, 2);
lean_inc(x_73);
x_3 = x_73;
goto block_8;
}
case 7:
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 2);
lean_inc(x_74);
x_3 = x_74;
goto block_8;
}
case 8:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
x_3 = x_75;
goto block_8;
}
case 9:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
x_3 = x_76;
goto block_8;
}
default: 
{
lean_inc(x_2);
x_3 = x_2;
goto block_8;
}
}
}
else
{
return x_2;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(13);
x_5 = l_Lean_IR_FnBody_setBody(x_2, x_4);
x_6 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_3);
x_7 = l_Lean_IR_FnBody_setBody(x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
x_8 = x_7;
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_1);
x_16 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_3);
x_8 = x_16;
goto block_12;
}
}
else
{
lean_dec(x_1);
return x_7;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_5, x_9);
x_5 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_10);
x_11 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_3);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_9;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = lean_unbox(x_7);
x_19 = lean_unbox(x_8);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(x_6, x_18, x_19, x_3, x_16, x_17, x_9);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(x_1, x_8, x_9, x_4, x_10, x_11, x_7);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_mkFresh___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_mkFresh(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_IR_ExpandResetReuse_mkFresh___redArg(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(7);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_13);
x_20 = lean_box(1);
lean_inc(x_17);
x_21 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_5);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_8);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_21);
x_4 = x_11;
x_5 = x_23;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_box(7);
lean_inc(x_2);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_box(1);
lean_inc(x_25);
x_30 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_5);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_8);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_30);
x_4 = x_11;
x_5 = x_32;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(x_2, x_1, x_6, x_6, x_3, x_5);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = lean_array_fget(x_1, x_10);
lean_inc(x_2);
x_12 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_5);
x_4 = x_9;
x_5 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(x_2, x_1, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_setFields(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_5);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_5, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 3)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_eq(x_25, x_3);
lean_dec(x_25);
if (x_27 == 0)
{
lean_dec(x_26);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_eq(x_26, x_2);
lean_dec(x_26);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_4, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_dec_eq(x_24, x_3);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_25, x_2);
lean_dec(x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_5);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_5, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_3, x_25);
lean_dec(x_25);
if (x_31 == 0)
{
lean_dec(x_26);
x_28 = x_31;
goto block_30;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_eq(x_26, x_4);
lean_dec(x_26);
x_28 = x_32;
goto block_30;
}
block_30:
{
if (x_28 == 0)
{
lean_dec(x_27);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_27, x_2);
lean_dec(x_27);
return x_29;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_24);
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_16);
lean_ctor_set(x_6, 1, x_17);
x_9 = x_6;
goto block_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_9 = x_21;
goto block_14;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_23);
lean_ctor_set(x_6, 0, x_24);
x_9 = x_6;
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_9 = x_27;
goto block_14;
}
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_10, x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_13);
lean_ctor_set(x_2, 3, x_15);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_21 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_17, x_18, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_20);
x_23 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_22);
return x_23;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_2 = x_20;
goto _start;
}
}
}
case 4:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
x_30 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_26, x_27, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_29);
lean_ctor_set(x_2, 3, x_31);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_2 = x_29;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_37 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_33, x_34, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_36);
x_39 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_38);
return x_39;
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_2 = x_36;
goto _start;
}
}
}
case 5:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get(x_2, 3);
x_46 = lean_ctor_get(x_2, 4);
x_47 = lean_ctor_get(x_2, 5);
x_48 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_42, x_43, x_44, x_45);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_47);
lean_ctor_set(x_2, 5, x_49);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_2 = x_47;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
x_55 = lean_ctor_get(x_2, 4);
x_56 = lean_ctor_get(x_2, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_57 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_51, x_52, x_53, x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_56);
x_59 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set(x_59, 5, x_58);
return x_59;
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_2 = x_56;
goto _start;
}
}
}
case 10:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_array_size(x_62);
x_64 = 0;
x_65 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(x_1, x_63, x_64, x_62);
lean_ctor_set(x_2, 3, x_65);
return x_2;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
x_68 = lean_ctor_get(x_2, 2);
x_69 = lean_ctor_get(x_2, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_2);
x_70 = lean_array_size(x_69);
x_71 = 0;
x_72 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(x_1, x_70, x_71, x_69);
x_73 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set(x_73, 3, x_72);
return x_73;
}
}
default: 
{
uint8_t x_74; 
x_74 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_74 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_2, 3);
lean_inc(x_75);
x_3 = x_75;
goto block_8;
}
case 1:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_2, 3);
lean_inc(x_76);
x_3 = x_76;
goto block_8;
}
case 2:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_2, 3);
lean_inc(x_77);
x_3 = x_77;
goto block_8;
}
case 3:
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_3 = x_78;
goto block_8;
}
case 4:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_2, 3);
lean_inc(x_79);
x_3 = x_79;
goto block_8;
}
case 5:
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_2, 5);
lean_inc(x_80);
x_3 = x_80;
goto block_8;
}
case 6:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_3 = x_81;
goto block_8;
}
case 7:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_2, 2);
lean_inc(x_82);
x_3 = x_82;
goto block_8;
}
case 8:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
x_3 = x_83;
goto block_8;
}
case 9:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
x_3 = x_84;
goto block_8;
}
default: 
{
lean_inc(x_2);
x_3 = x_2;
goto block_8;
}
}
}
else
{
return x_2;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(13);
x_5 = l_Lean_IR_FnBody_setBody(x_2, x_4);
x_6 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_3);
x_7 = l_Lean_IR_FnBody_setBody(x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_6, x_5, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_3);
x_19 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_18);
lean_ctor_set(x_8, 1, x_19);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
lean_inc(x_3);
x_22 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_11 = x_23;
goto block_16;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_3);
x_26 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_25);
lean_ctor_set(x_8, 0, x_26);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
lean_inc(x_3);
x_28 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_11 = x_29;
goto block_16;
}
}
block_16:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_14 = lean_array_uset(x_10, x_5, x_11);
x_5 = x_13;
x_6 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 2)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_20 = lean_ctor_get(x_11, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_2, x_17);
lean_dec(x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_15);
lean_ctor_set(x_4, 3, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_11);
lean_inc(x_3);
x_23 = l_Lean_IR_FnBody_replaceVar(x_13, x_3, x_15);
lean_inc(x_3);
x_24 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_20, x_23);
lean_dec(x_20);
if (x_19 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_3);
x_25 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
x_28 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_ctor_get(x_4, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_35 = lean_ctor_get(x_11, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_eq(x_2, x_32);
lean_dec(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_33);
x_37 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_31);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_11);
lean_ctor_set(x_38, 3, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_11);
lean_inc(x_3);
x_39 = l_Lean_IR_FnBody_replaceVar(x_29, x_3, x_31);
lean_inc(x_3);
x_40 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_35, x_39);
lean_dec(x_35);
if (x_34 == 0)
{
lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_3);
x_41 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
x_44 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 2);
lean_dec(x_47);
x_48 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_46);
lean_ctor_set(x_4, 3, x_48);
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_ctor_get(x_4, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_4);
x_52 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_51);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_11);
lean_ctor_set(x_53, 3, x_52);
return x_53;
}
}
}
case 7:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_nat_dec_eq(x_2, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_57);
lean_ctor_set(x_4, 2, x_59);
return x_4;
}
else
{
lean_object* x_60; 
lean_free_object(x_4);
lean_dec(x_56);
lean_dec(x_55);
x_60 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_65 = lean_ctor_get(x_4, 2);
lean_inc(x_65);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_66 = lean_nat_dec_eq(x_2, x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_65);
x_68 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*3 + 1, x_64);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_61);
x_69 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
case 10:
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_4);
if (x_70 == 0)
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_4, 3);
x_72 = lean_array_size(x_71);
x_73 = 0;
x_74 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(x_1, x_2, x_3, x_72, x_73, x_71);
lean_ctor_set(x_4, 3, x_74);
return x_4;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_4, 0);
x_76 = lean_ctor_get(x_4, 1);
x_77 = lean_ctor_get(x_4, 2);
x_78 = lean_ctor_get(x_4, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_4);
x_79 = lean_array_size(x_78);
x_80 = 0;
x_81 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(x_1, x_2, x_3, x_79, x_80, x_78);
x_82 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_81);
return x_82;
}
}
default: 
{
uint8_t x_83; 
x_83 = l_Lean_IR_FnBody_isTerminal(x_4);
if (x_83 == 0)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_4, 3);
lean_inc(x_84);
x_5 = x_84;
goto block_10;
}
case 1:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_4, 3);
lean_inc(x_85);
x_5 = x_85;
goto block_10;
}
case 2:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_4, 3);
lean_inc(x_86);
x_5 = x_86;
goto block_10;
}
case 3:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_4, 2);
lean_inc(x_87);
x_5 = x_87;
goto block_10;
}
case 4:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_4, 3);
lean_inc(x_88);
x_5 = x_88;
goto block_10;
}
case 5:
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_4, 5);
lean_inc(x_89);
x_5 = x_89;
goto block_10;
}
case 6:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_4, 2);
lean_inc(x_90);
x_5 = x_90;
goto block_10;
}
case 7:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_4, 2);
lean_inc(x_91);
x_5 = x_91;
goto block_10;
}
case 8:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 1);
lean_inc(x_92);
x_5 = x_92;
goto block_10;
}
case 9:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
x_5 = x_93;
goto block_10;
}
default: 
{
lean_inc(x_4);
x_5 = x_4;
goto block_10;
}
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(13);
x_7 = l_Lean_IR_FnBody_setBody(x_4, x_6);
x_8 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_5);
x_9 = l_Lean_IR_FnBody_setBody(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_5, x_1, x_2, x_4);
x_8 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_4, x_5, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_3, x_5, x_11, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
x_16 = lean_apply_4(x_1, x_13, x_15, x_7, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_IR_ExpandResetReuse_mkFresh___redArg(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_5);
x_22 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_dec(x_11);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_24, 0, x_5);
lean_inc(x_21);
x_25 = l_Lean_IR_mkIf(x_21, x_22, x_17);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = l_Lean_IR_reshape(x_10, x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
lean_inc(x_5);
x_30 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_dec(x_11);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_32, 0, x_5);
lean_inc(x_28);
x_33 = l_Lean_IR_mkIf(x_28, x_30, x_17);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = l_Lean_IR_reshape(x_10, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_expand(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_4, x_3);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_4, x_3, x_10);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_1);
lean_inc(x_5);
x_21 = lean_apply_3(x_1, x_20, x_5, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_9, 1, x_22);
x_12 = x_9;
x_13 = x_23;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_5);
x_26 = lean_apply_3(x_1, x_25, x_5, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_27);
x_12 = x_29;
x_13 = x_28;
goto block_18;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_1);
lean_inc(x_5);
x_32 = lean_apply_3(x_1, x_31, x_5, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_9, 0, x_33);
x_12 = x_9;
x_13 = x_34;
goto block_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_5);
x_36 = lean_apply_3(x_1, x_35, x_5, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_12 = x_39;
x_13 = x_38;
goto block_18;
}
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_11, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_6 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
x_5 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_IR_ExpandResetReuse_consumed(x_32, x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_37 = l_Lean_IR_push(x_2, x_1);
x_1 = x_33;
x_2 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand), 4, 0);
x_40 = l_Lean_IR_ExpandResetReuse_expand(x_39, x_2, x_32, x_34, x_35, x_33, x_3, x_4);
lean_dec(x_32);
return x_40;
}
}
else
{
lean_dec(x_31);
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_30;
}
}
case 1:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get(x_1, 3);
x_44 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
lean_inc(x_3);
x_45 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_42, x_44, x_3, x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(13);
lean_ctor_set(x_1, 3, x_48);
lean_ctor_set(x_1, 2, x_46);
x_49 = l_Lean_IR_push(x_2, x_1);
x_1 = x_43;
x_2 = x_49;
x_4 = x_47;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get(x_1, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_55 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
lean_inc(x_3);
x_56 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_53, x_55, x_3, x_4);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_box(13);
x_60 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_Lean_IR_push(x_2, x_60);
x_1 = x_54;
x_2 = x_61;
x_4 = x_58;
goto _start;
}
}
case 10:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_1, 3);
x_65 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand___lam__0), 3, 0);
x_66 = lean_array_size(x_64);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(x_65, x_66, x_67, x_64, x_3, x_4);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_ctor_set(x_1, 3, x_70);
x_71 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
lean_ctor_set(x_1, 3, x_72);
x_74 = l_Lean_IR_reshape(x_2, x_1);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_1, 0);
x_77 = lean_ctor_get(x_1, 1);
x_78 = lean_ctor_get(x_1, 2);
x_79 = lean_ctor_get(x_1, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_1);
x_80 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand___lam__0), 3, 0);
x_81 = lean_array_size(x_79);
x_82 = 0;
x_83 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(x_80, x_81, x_82, x_79, x_3, x_4);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_77);
lean_ctor_set(x_87, 2, x_78);
lean_ctor_set(x_87, 3, x_84);
x_88 = l_Lean_IR_reshape(x_2, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_30;
}
}
block_12:
{
lean_object* x_10; 
x_10 = l_Lean_IR_push(x_6, x_8);
x_1 = x_9;
x_2 = x_10;
x_3 = x_7;
x_4 = x_5;
goto _start;
}
block_30:
{
uint8_t x_17; 
x_17 = l_Lean_IR_FnBody_isTerminal(x_13);
if (x_17 == 0)
{
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_18;
goto block_12;
}
case 1:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_19;
goto block_12;
}
case 2:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_20;
goto block_12;
}
case 3:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_21;
goto block_12;
}
case 4:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_13, 3);
lean_inc(x_22);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_22;
goto block_12;
}
case 5:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_13, 5);
lean_inc(x_23);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_23;
goto block_12;
}
case 6:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_24;
goto block_12;
}
case 7:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_13, 2);
lean_inc(x_25);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_25;
goto block_12;
}
case 8:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_26;
goto block_12;
}
case 9:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_27;
goto block_12;
}
default: 
{
lean_inc(x_13);
x_5 = x_16;
x_6 = x_14;
x_7 = x_15;
x_8 = x_13;
x_9 = x_13;
goto block_12;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_28 = l_Lean_IR_reshape(x_14, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_1);
lean_inc(x_1);
x_4 = l_Lean_IR_Decl_maxIndex(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0;
x_8 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_2, x_7, x_3, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_Decl_updateBody_x21(x_1, x_9);
return x_10;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_main(x_1);
x_3 = l_Lean_IR_Decl_normalizeIds(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__0 = _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__0();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__0);
l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1 = _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__0 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__0();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__0);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__4);
l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0 = _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
