// Lean compiler output
// Module: Lean.Compiler.IR.ExpandResetReuse
// Imports: Init Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds Lean.Compiler.IR.FreeVars
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
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_instBEqVarId___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_instHashableVarId___boxed(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___at_Lean_IR_FnBody_replaceVar___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___spec__1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1;
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instBEqVarId___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
x_5 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
x_6 = l_Std_HashMap_insert___rarg(x_4, x_5, x_3, x_1, x_2);
return x_6;
}
case 4:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
x_8 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
x_9 = l_Std_HashMap_insert___rarg(x_7, x_8, x_3, x_1, x_2);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
x_11 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
x_12 = l_Std_HashMap_insert___rarg(x_10, x_11, x_3, x_1, x_2);
return x_12;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_8 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_7, x_4);
x_9 = 1;
x_10 = x_2 + x_9;
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
x_8 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
x_9 = l_Std_HashMap_insert___rarg(x_7, x_8, x_6, x_3, x_4);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
x_11 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
x_12 = l_Std_HashMap_insert___rarg(x_10, x_11, x_6, x_3, x_4);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1;
x_14 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2;
x_15 = l_Std_HashMap_insert___rarg(x_13, x_14, x_6, x_3, x_4);
return x_15;
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_17, x_2);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
case 10:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(x_20, x_25, x_26, x_2);
lean_dec(x_20);
return x_27;
}
}
}
default: 
{
uint8_t x_28; 
x_28 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_29;
goto _start;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
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
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_8 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
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
lean_inc(x_3);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_nat_dec_eq(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
case 7:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_nat_dec_eq(x_1, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
}
case 10:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = 1;
return x_22;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(x_1, x_16, x_23, x_24);
lean_dec(x_16);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
}
}
default: 
{
uint8_t x_28; 
x_28 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_29;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = 0;
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(x_1, x_2, x_5, x_6);
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
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_IR_instInhabitedFnBody;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___spec__1(x_2);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 4:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
x_10 = lean_array_pop(x_2);
x_11 = lean_array_push(x_4, x_8);
x_2 = x_10;
x_4 = x_11;
goto _start;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_array_pop(x_2);
x_14 = lean_array_push(x_4, x_8);
x_2 = x_13;
x_4 = x_14;
goto _start;
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
x_16 = l_Array_reverse___rarg(x_4);
x_17 = l_Array_append___rarg(x_2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
case 6:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_26 = l_Lean_IR_instInhabitedFnBody;
x_27 = lean_array_get(x_26, x_2, x_25);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 3)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_nat_dec_eq(x_29, x_20);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_20);
x_33 = l_Array_reverse___rarg(x_4);
x_34 = l_Array_append___rarg(x_2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_eq(x_1, x_31);
lean_dec(x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_20);
x_37 = l_Array_reverse___rarg(x_4);
x_38 = l_Array_append___rarg(x_2, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_array_pop(x_2);
x_41 = lean_array_pop(x_40);
lean_inc(x_20);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_20);
x_43 = lean_array_set(x_3, x_30, x_42);
lean_dec(x_30);
x_44 = lean_array_push(x_4, x_27);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_dec_eq(x_21, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_sub(x_21, x_45);
lean_dec(x_21);
x_48 = lean_box(13);
lean_ctor_set(x_8, 2, x_48);
lean_ctor_set(x_8, 1, x_47);
x_49 = lean_array_push(x_44, x_8);
x_2 = x_41;
x_3 = x_43;
x_4 = x_49;
goto _start;
}
else
{
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_20);
x_2 = x_41;
x_3 = x_43;
x_4 = x_44;
goto _start;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_20);
x_52 = l_Array_reverse___rarg(x_4);
x_53 = l_Array_append___rarg(x_2, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_20);
x_55 = l_Array_reverse___rarg(x_4);
x_56 = l_Array_append___rarg(x_2, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_58 = l_Array_reverse___rarg(x_4);
x_59 = l_Array_append___rarg(x_2, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_8, 0);
x_62 = lean_ctor_get(x_8, 1);
x_63 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_64 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_8);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_68 = l_Lean_IR_instInhabitedFnBody;
x_69 = lean_array_get(x_68, x_2, x_67);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 2);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 3)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_nat_dec_eq(x_71, x_61);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_62);
lean_dec(x_61);
x_75 = l_Array_reverse___rarg(x_4);
x_76 = l_Array_append___rarg(x_2, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_3);
return x_77;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_eq(x_1, x_73);
lean_dec(x_73);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_62);
lean_dec(x_61);
x_79 = l_Array_reverse___rarg(x_4);
x_80 = l_Array_append___rarg(x_2, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_3);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_82 = lean_array_pop(x_2);
x_83 = lean_array_pop(x_82);
lean_inc(x_61);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_61);
x_85 = lean_array_set(x_3, x_72, x_84);
lean_dec(x_72);
x_86 = lean_array_push(x_4, x_69);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_dec_eq(x_62, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_nat_sub(x_62, x_87);
lean_dec(x_62);
x_90 = lean_box(13);
x_91 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_91, 0, x_61);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_63);
lean_ctor_set_uint8(x_91, sizeof(void*)*3 + 1, x_64);
x_92 = lean_array_push(x_86, x_91);
x_2 = x_83;
x_3 = x_85;
x_4 = x_92;
goto _start;
}
else
{
lean_dec(x_62);
lean_dec(x_61);
x_2 = x_83;
x_3 = x_85;
x_4 = x_86;
goto _start;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_62);
lean_dec(x_61);
x_95 = l_Array_reverse___rarg(x_4);
x_96 = l_Array_append___rarg(x_2, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_69);
lean_dec(x_62);
lean_dec(x_61);
x_98 = l_Array_reverse___rarg(x_4);
x_99 = l_Array_append___rarg(x_2, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_3);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
x_101 = l_Array_reverse___rarg(x_4);
x_102 = l_Array_append___rarg(x_2, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_3);
return x_103;
}
}
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_8);
lean_dec(x_5);
x_104 = l_Array_reverse___rarg(x_4);
x_105 = l_Array_append___rarg(x_2, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_3);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_5);
x_107 = l_Array_reverse___rarg(x_4);
x_108 = l_Array_append___rarg(x_2, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_3);
return x_109;
}
}
}
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___spec__1(x_1);
lean_dec(x_1);
return x_2;
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
static lean_object* _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1() {
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
x_6 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = 1;
x_12 = x_3 + x_11;
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_14);
lean_ctor_set(x_10, 1, x_15);
x_16 = x_10;
x_17 = lean_array_uset(x_9, x_3, x_16);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = x_22;
x_24 = lean_array_uset(x_9, x_3, x_23);
x_3 = x_12;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = x_10;
x_30 = lean_array_uset(x_9, x_3, x_29);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
x_33 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = x_34;
x_36 = lean_array_uset(x_9, x_3, x_35);
x_3 = x_12;
x_4 = x_36;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_1, x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_5);
lean_ctor_set(x_2, 3, x_11);
return x_2;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_2, 2, x_12);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_1, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_15);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_15);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 3);
x_26 = lean_ctor_get(x_2, 2);
lean_dec(x_26);
x_27 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_25);
lean_ctor_set(x_2, 3, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_31 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_31);
return x_32;
}
}
}
case 7:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_nat_dec_eq(x_1, x_34);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_36);
lean_ctor_set(x_2, 2, x_38);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_34);
return x_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_44 = lean_nat_dec_eq(x_1, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_43);
x_46 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_42);
return x_46;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
return x_43;
}
}
}
case 10:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_array_get_size(x_48);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = 0;
x_52 = x_48;
x_53 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_50, x_51, x_52);
x_54 = x_53;
lean_ctor_set(x_2, 3, x_54);
return x_2;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
x_58 = lean_ctor_get(x_2, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_59 = lean_array_get_size(x_58);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
x_62 = x_58;
x_63 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_60, x_61, x_62);
x_64 = x_63;
x_65 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_56);
lean_ctor_set(x_65, 2, x_57);
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l_Lean_IR_FnBody_body(x_2);
x_68 = lean_box(13);
x_69 = l_Lean_IR_FnBody_setBody(x_2, x_68);
x_70 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_67);
x_71 = l_Lean_IR_FnBody_setBody(x_69, x_70);
return x_71;
}
else
{
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_5, x_6, x_4);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_13);
x_2 = x_8;
x_4 = x_14;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_4);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = 1;
x_8 = 0;
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_8);
x_10 = lean_array_get_size(x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
return x_9;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
return x_9;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_3, x_14, x_15, x_9);
lean_dec(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_mkFresh___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_array_get(x_14, x_2, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_1);
x_20 = 1;
x_21 = 0;
lean_inc(x_17);
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_21);
x_23 = lean_box(7);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_22);
x_4 = x_11;
x_5 = x_24;
x_7 = x_18;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_6, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_instInhabitedArg;
x_13 = lean_array_get(x_12, x_2, x_11);
lean_inc(x_1);
x_14 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_5);
x_4 = x_9;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_foldAux___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 3)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_nat_dec_eq(x_9, x_3);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_10, x_2);
lean_dec(x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = 0;
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_8, x_3);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_9, x_2);
lean_dec(x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_nat_dec_eq(x_3, x_9);
lean_dec(x_9);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_4);
lean_dec(x_10);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_11, x_2);
lean_dec(x_11);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = 0;
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = 1;
x_12 = x_3 + x_11;
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_1);
x_15 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_14);
lean_ctor_set(x_10, 1, x_15);
x_16 = x_10;
x_17 = lean_array_uset(x_9, x_3, x_16);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_1);
x_21 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = x_22;
x_24 = lean_array_uset(x_9, x_3, x_23);
x_3 = x_12;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_1);
x_28 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = x_10;
x_30 = lean_array_uset(x_9, x_3, x_29);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
lean_inc(x_1);
x_33 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = x_34;
x_36 = lean_array_uset(x_9, x_3, x_35);
x_3 = x_12;
x_4 = x_36;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_4, x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_7);
lean_ctor_set(x_2, 3, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_13);
lean_inc(x_1);
x_15 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_11, x_12, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_14);
x_17 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_2 = x_14;
goto _start;
}
}
}
case 4:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_inc(x_1);
x_24 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_20, x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_23);
lean_ctor_set(x_2, 3, x_25);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_2 = x_23;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_29);
lean_inc(x_1);
x_31 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_27, x_28, x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_30);
x_33 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_32);
return x_33;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_2 = x_30;
goto _start;
}
}
}
case 5:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 3);
x_40 = lean_ctor_get(x_2, 4);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_39);
lean_inc(x_1);
x_42 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_36, x_37, x_38, x_39);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_41);
lean_ctor_set(x_2, 5, x_43);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_2 = x_41;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_ctor_get(x_2, 4);
x_50 = lean_ctor_get(x_2, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
lean_inc(x_48);
lean_inc(x_1);
x_51 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_45, x_46, x_47, x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_50);
x_53 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_52);
return x_53;
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_2 = x_50;
goto _start;
}
}
}
case 10:
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
x_60 = x_56;
x_61 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_58, x_59, x_60);
x_62 = x_61;
lean_ctor_set(x_2, 3, x_62);
return x_2;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
x_65 = lean_ctor_get(x_2, 2);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_2);
x_67 = lean_array_get_size(x_66);
x_68 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_69 = 0;
x_70 = x_66;
x_71 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_68, x_69, x_70);
x_72 = x_71;
x_73 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_65);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = l_Lean_IR_FnBody_body(x_2);
x_76 = lean_box(13);
x_77 = l_Lean_IR_FnBody_setBody(x_2, x_76);
x_78 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_75);
x_79 = l_Lean_IR_FnBody_setBody(x_77, x_78);
return x_79;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = x_6;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = 1;
x_14 = x_5 + x_13;
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_16);
lean_ctor_set(x_12, 1, x_17);
x_18 = x_12;
x_19 = lean_array_uset(x_11, x_5, x_18);
x_5 = x_14;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
lean_inc(x_3);
lean_inc(x_1);
x_23 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = x_24;
x_26 = lean_array_uset(x_11, x_5, x_25);
x_5 = x_14;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_3);
lean_inc(x_1);
x_30 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_29);
lean_ctor_set(x_12, 0, x_30);
x_31 = x_12;
x_32 = lean_array_uset(x_11, x_5, x_31);
x_5 = x_14;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = x_36;
x_38 = lean_array_uset(x_11, x_5, x_37);
x_5 = x_14;
x_6 = x_38;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_ctor_get(x_4, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_2, x_11);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_9);
lean_ctor_set(x_4, 3, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_5);
lean_inc(x_3);
x_17 = l_Lean_IR_MapVars_mapFnBody___at_Lean_IR_FnBody_replaceVar___spec__1(x_7, x_3, x_9);
lean_dec(x_7);
lean_inc(x_3);
x_18 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_14, x_17);
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_3);
x_19 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
x_22 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_29 = lean_ctor_get(x_5, 2);
lean_inc(x_29);
x_30 = lean_nat_dec_eq(x_2, x_26);
lean_dec(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_27);
x_31 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_25);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_5);
lean_ctor_set(x_32, 3, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_5);
lean_inc(x_3);
x_33 = l_Lean_IR_MapVars_mapFnBody___at_Lean_IR_FnBody_replaceVar___spec__1(x_23, x_3, x_25);
lean_dec(x_23);
lean_inc(x_3);
x_34 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_29, x_33);
lean_dec(x_29);
if (x_28 == 0)
{
lean_object* x_35; 
lean_dec(x_27);
lean_dec(x_3);
x_35 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_34);
x_38 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_4, 3);
x_41 = lean_ctor_get(x_4, 2);
lean_dec(x_41);
x_42 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_40);
lean_ctor_set(x_4, 3, x_42);
return x_4;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
x_45 = lean_ctor_get(x_4, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_46 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_5);
lean_ctor_set(x_47, 3, x_46);
return x_47;
}
}
}
case 7:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_ctor_get(x_4, 2);
x_52 = lean_nat_dec_eq(x_2, x_49);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_51);
lean_ctor_set(x_4, 2, x_53);
return x_4;
}
else
{
lean_object* x_54; 
lean_free_object(x_4);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_1);
x_54 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_59 = lean_ctor_get(x_4, 2);
lean_inc(x_59);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_4);
x_60 = lean_nat_dec_eq(x_2, x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_59);
x_62 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 1, x_58);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_1);
x_63 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
case 10:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_4, 3);
x_66 = lean_array_get_size(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = 0;
x_69 = x_65;
x_70 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_67, x_68, x_69);
x_71 = x_70;
lean_ctor_set(x_4, 3, x_71);
return x_4;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_72 = lean_ctor_get(x_4, 0);
x_73 = lean_ctor_get(x_4, 1);
x_74 = lean_ctor_get(x_4, 2);
x_75 = lean_ctor_get(x_4, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_4);
x_76 = lean_array_get_size(x_75);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = 0;
x_79 = x_75;
x_80 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_77, x_78, x_79);
x_81 = x_80;
x_82 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_82, 2, x_74);
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
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = l_Lean_IR_FnBody_body(x_4);
x_85 = lean_box(13);
x_86 = l_Lean_IR_FnBody_setBody(x_4, x_85);
x_87 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_84);
x_88 = l_Lean_IR_FnBody_setBody(x_86, x_87);
return x_88;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_5);
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
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_4, x_5, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_inc(x_7);
lean_inc(x_5);
x_13 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_3, x_5, x_11, x_6, x_7, x_8);
lean_dec(x_11);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
x_17 = lean_apply_4(x_1, x_14, x_16, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_23, 0, x_5);
lean_inc(x_22);
x_24 = l_Lean_IR_mkIf(x_22, x_12, x_18);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l_Lean_IR_reshape(x_10, x_26);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_30, 0, x_5);
lean_inc(x_28);
x_31 = l_Lean_IR_mkIf(x_28, x_12, x_18);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Lean_IR_reshape(x_10, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_2 < x_1;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = x_3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = x_9;
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_16 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_14, x_15, x_4, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_17);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = x_12;
x_22 = lean_array_uset(x_11, x_2, x_21);
x_2 = x_20;
x_3 = x_22;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_27 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_25, x_26, x_4, x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
x_31 = 1;
x_32 = x_2 + x_31;
x_33 = x_30;
x_34 = lean_array_uset(x_11, x_2, x_33);
x_2 = x_32;
x_3 = x_34;
x_5 = x_29;
goto _start;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_39 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_37, x_38, x_4, x_5);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_ctor_set(x_12, 0, x_40);
x_42 = 1;
x_43 = x_2 + x_42;
x_44 = x_12;
x_45 = lean_array_uset(x_11, x_2, x_44);
x_2 = x_43;
x_3 = x_45;
x_5 = x_41;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
lean_dec(x_12);
x_48 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_49 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_47, x_48, x_4, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = 1;
x_54 = x_2 + x_53;
x_55 = x_52;
x_56 = lean_array_uset(x_11, x_2, x_55);
x_2 = x_54;
x_3 = x_56;
x_5 = x_51;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_7);
x_10 = l_Lean_IR_ExpandResetReuse_consumed(x_6, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = l_Lean_IR_push(x_2, x_1);
x_1 = x_7;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1;
x_14 = l_Lean_IR_ExpandResetReuse_expand(x_13, x_2, x_6, x_8, x_9, x_7, x_3, x_4);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_IR_FnBody_body(x_1);
x_17 = l_Lean_IR_push(x_2, x_1);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = l_Lean_IR_reshape(x_2, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
}
case 1:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
x_24 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_3);
x_25 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_22, x_24, x_3, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(13);
lean_ctor_set(x_1, 3, x_28);
lean_ctor_set(x_1, 2, x_26);
x_29 = l_Lean_IR_push(x_2, x_1);
x_1 = x_23;
x_2 = x_29;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_35 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_3);
x_36 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_33, x_35, x_3, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(13);
x_40 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Lean_IR_push(x_2, x_40);
x_1 = x_34;
x_2 = x_41;
x_4 = x_38;
goto _start;
}
}
case 10:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = x_44;
x_48 = lean_box_usize(x_46);
x_49 = l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1;
x_50 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed), 5, 3);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_49);
lean_closure_set(x_50, 2, x_47);
x_51 = x_50;
x_52 = lean_apply_2(x_51, x_3, x_4);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_1, 3, x_54);
x_55 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
lean_ctor_set(x_1, 3, x_56);
x_58 = l_Lean_IR_reshape(x_2, x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 1);
x_62 = lean_ctor_get(x_1, 2);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_1);
x_64 = lean_array_get_size(x_63);
x_65 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_66 = x_63;
x_67 = lean_box_usize(x_65);
x_68 = l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1;
x_69 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed), 5, 3);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
lean_closure_set(x_69, 2, x_66);
x_70 = x_69;
x_71 = lean_apply_2(x_70, x_3, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_61);
lean_ctor_set(x_75, 2, x_62);
lean_ctor_set(x_75, 3, x_72);
x_76 = l_Lean_IR_reshape(x_2, x_75);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
default: 
{
uint8_t x_78; 
x_78 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_IR_FnBody_body(x_1);
x_80 = l_Lean_IR_push(x_2, x_1);
x_1 = x_79;
x_2 = x_80;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_3);
x_82 = l_Lean_IR_reshape(x_2, x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_4);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
x_9 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_2, x_8, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_Decl_updateBody_x21(x_1, x_10);
return x_11;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1 = _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__1);
l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2 = _init_l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___closed__2);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1);
l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1 = _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1);
l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1 = _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1);
l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1 = _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_searchAndExpand___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
