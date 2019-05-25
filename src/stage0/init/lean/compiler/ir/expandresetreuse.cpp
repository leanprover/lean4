// Lean compiler output
// Module: init.lean.compiler.ir.expandresetreuse
// Imports: init.control.state init.control.reader init.lean.compiler.ir.compilerm init.lean.compiler.ir.normids init.lean.compiler.ir.freevars
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_expandResetReuse(obj*);
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkFastPath(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_setFields(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_ExpandResetReuse_isSelfUSet(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkProjMap(obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
uint8 l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(obj*, obj*);
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_expand(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1___boxed(obj*);
obj* l_Lean_IR_ExpandResetReuse_mkFresh(obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkSlowPath(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(obj*, obj*, obj*);
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_ExpandResetReuse_consumed(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToSet(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_consumed___boxed(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___main___boxed(obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_IR_mkIf(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main(obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet(obj*, obj*);
uint8 l_Lean_IR_ExpandResetReuse_consumed___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(obj*);
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_main(obj*);
obj* l_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
uint8 l_Lean_IR_ExpandResetReuse_isSelfSet(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(obj*, obj*, obj*);
obj* l_Array_pop(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_expand___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main___boxed(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_Lean_IR_push(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1;
uint8 l_Lean_IR_ExpandResetReuse_isSelfSSet(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(obj*, obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_setFields___boxed(obj*, obj*, obj*);
extern obj* l_Lean_IR_Arg_Inhabited;
extern obj* l_Lean_IR_Inhabited;
uint8 l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
uint8 x_7; 
x_2 = x_5;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::array_get_size(x_1);
x_7 = lean::usize_of_nat(x_4);
x_8 = lean::usize_modn(x_7, x_6);
lean::dec(x_6);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean::array_uget(x_1, x_10);
lean::cnstr_set(x_2, 2, x_11);
x_12 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_13 = lean::array_uset(x_1, x_12, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; obj* x_27; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::array_get_size(x_1);
x_19 = lean::usize_of_nat(x_15);
x_20 = lean::usize_modn(x_19, x_18);
lean::dec(x_18);
x_21 = lean::box_size_t(x_20);
x_22 = lean::unbox_size_t(x_21);
x_23 = lean::array_uget(x_1, x_22);
x_24 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_26 = lean::array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldl___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(x_3, x_6);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_5, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 2);
x_8 = lean::nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_7);
lean::cnstr_set(x_3, 2, x_9);
return x_3;
}
else
{
lean::dec(x_6);
lean::dec(x_5);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_12);
x_15 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_10);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::array_get_size(x_6);
x_8 = lean::usize_of_nat(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_2, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; usize x_17; obj* x_18; uint8 x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_12);
x_17 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_18 = lean::array_uset(x_6, x_17, x_16);
x_19 = lean::nat_dec_le(x_15, x_7);
lean::dec(x_7);
if (x_19 == 0)
{
obj* x_20; 
lean::free_heap_obj(x_1);
x_20 = l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_15, x_18);
return x_20;
}
else
{
lean::cnstr_set(x_1, 1, x_18);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_21; usize x_22; obj* x_23; 
lean::dec(x_7);
x_21 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_2, x_3, x_12);
x_22 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_23 = lean::array_uset(x_6, x_22, x_21);
lean::cnstr_set(x_1, 1, x_23);
return x_1;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; usize x_27; usize x_28; obj* x_29; usize x_30; obj* x_31; uint8 x_32; 
x_24 = lean::cnstr_get(x_1, 0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_1);
x_26 = lean::array_get_size(x_25);
x_27 = lean::usize_of_nat(x_2);
x_28 = lean::usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean::array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_2, x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; usize x_36; obj* x_37; uint8 x_38; 
x_33 = lean::mk_nat_obj(1u);
x_34 = lean::nat_add(x_24, x_33);
lean::dec(x_24);
x_35 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_31);
x_36 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_37 = lean::array_uset(x_25, x_36, x_35);
x_38 = lean::nat_dec_le(x_34, x_26);
lean::dec(x_26);
if (x_38 == 0)
{
obj* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_34, x_37);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_34);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
else
{
obj* x_41; usize x_42; obj* x_43; obj* x_44; 
lean::dec(x_26);
x_41 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_2, x_3, x_31);
x_42 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_43 = lean::array_uset(x_25, x_42, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_4; 
x_4 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_4;
}
case 4:
{
obj* x_5; 
x_5 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_5;
}
case 5:
{
obj* x_6; 
x_6 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_6;
}
default: 
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_9 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_8, x_4);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::dec(x_1);
x_11 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_10, x_2);
switch (lean::obj_tag(x_9)) {
case 3:
{
obj* x_12; 
x_12 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_11, x_8, x_9);
return x_12;
}
case 4:
{
obj* x_13; 
x_13 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_11, x_8, x_9);
return x_13;
}
case 5:
{
obj* x_14; 
x_14 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_11, x_8, x_9);
return x_14;
}
default: 
{
lean::dec(x_9);
lean::dec(x_8);
return x_11;
}
}
}
case 1:
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_1, 2);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
lean::dec(x_1);
x_17 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_16, x_2);
x_1 = x_15;
x_2 = x_17;
goto _start;
}
case 10:
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
lean::dec(x_1);
x_20 = lean::mk_nat_obj(0u);
x_21 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(x_19, x_19, x_20, x_2);
lean::dec(x_19);
return x_21;
}
default: 
{
obj* x_22; 
x_22 = lean::box(0);
x_3 = x_22;
goto block_7;
}
}
block_7:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkProjMap(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
lean::dec(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_2, x_3);
return x_4;
}
else
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
return x_5;
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_9 = l_Lean_IR_ExpandResetReuse_consumed___main(x_1, x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_3);
x_10 = 1;
return x_10;
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
}
}
}
uint8 l_Lean_IR_ExpandResetReuse_consumed___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 2)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::cnstr_get(x_2, 2);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::nat_dec_eq(x_1, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_13; 
x_2 = x_10;
goto _start;
}
else
{
uint8 x_14; 
lean::dec(x_10);
x_14 = 1;
return x_14;
}
}
else
{
obj* x_15; uint8 x_16; 
lean::dec(x_9);
x_15 = lean::cnstr_get(x_2, 2);
lean::inc(x_15);
lean::dec(x_2);
x_2 = x_15;
goto _start;
}
}
case 7:
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_2, 2);
lean::inc(x_18);
lean::dec(x_2);
x_19 = lean::nat_dec_eq(x_1, x_17);
lean::dec(x_17);
if (x_19 == 0)
{
uint8 x_20; 
x_2 = x_18;
goto _start;
}
else
{
uint8 x_21; 
lean::dec(x_18);
x_21 = 1;
return x_21;
}
}
case 10:
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = lean::cnstr_get(x_2, 2);
lean::inc(x_22);
lean::dec(x_2);
x_23 = lean::mk_nat_obj(0u);
x_24 = l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_1, x_22, x_23);
lean::dec(x_22);
if (x_24 == 0)
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
else
{
uint8 x_26; 
x_26 = 0;
return x_26;
}
}
default: 
{
obj* x_27; 
x_27 = lean::box(0);
x_3 = x_27;
goto block_8;
}
}
block_8:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_4 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = l_Lean_IR_FnBody_body___main(x_2);
lean::dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed___main(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_ExpandResetReuse_consumed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_consumed___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean::array_get(x_5, x_1, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_11; obj* x_16; obj* x_17; uint8 x_18; 
x_16 = lean::array_get_size(x_2);
x_17 = lean::mk_nat_obj(2u);
x_18 = lean::nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
obj* x_19; 
x_19 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(x_2);
switch (lean::obj_tag(x_19)) {
case 0:
{
obj* x_20; 
lean::dec(x_16);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
switch (lean::obj_tag(x_20)) {
case 4:
{
lean::dec(x_20);
x_11 = x_19;
goto block_15;
}
case 5:
{
lean::dec(x_20);
x_11 = x_19;
goto block_15;
}
default: 
{
obj* x_21; 
lean::dec(x_20);
lean::dec(x_19);
x_21 = lean::box(0);
x_5 = x_21;
goto block_10;
}
}
}
case 6:
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; uint8 x_26; 
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_19, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*3);
lean::dec(x_19);
x_25 = lean::mk_nat_obj(0u);
x_26 = lean::nat_dec_eq(x_23, x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::nat_sub(x_16, x_17);
lean::dec(x_16);
x_28 = l_Lean_IR_Inhabited;
x_29 = lean::array_get(x_28, x_2, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; 
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 3)
{
obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_34 = lean::nat_dec_eq(x_31, x_22);
lean::dec(x_31);
if (x_34 == 0)
{
obj* x_35; 
lean::dec(x_33);
lean::dec(x_32);
lean::dec(x_29);
lean::dec(x_23);
lean::dec(x_22);
x_35 = lean::box(0);
x_5 = x_35;
goto block_10;
}
else
{
uint8 x_36; 
x_36 = lean::nat_dec_eq(x_1, x_33);
lean::dec(x_33);
if (x_36 == 0)
{
obj* x_37; 
lean::dec(x_32);
lean::dec(x_29);
lean::dec(x_23);
lean::dec(x_22);
x_37 = lean::box(0);
x_5 = x_37;
goto block_10;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; uint8 x_43; 
x_38 = lean::array_pop(x_2);
x_39 = lean::array_pop(x_38);
lean::inc(x_22);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_22);
x_41 = lean::array_set(x_3, x_32, x_40);
lean::dec(x_32);
x_42 = lean::mk_nat_obj(1u);
x_43 = lean::nat_dec_eq(x_23, x_42);
if (x_43 == 0)
{
obj* x_44; uint8 x_45; 
lean::inc(x_29);
x_44 = lean::array_push(x_4, x_29);
x_45 = !lean::is_exclusive(x_29);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_46 = lean::cnstr_get(x_29, 2);
lean::dec(x_46);
x_47 = lean::cnstr_get(x_29, 1);
lean::dec(x_47);
x_48 = lean::cnstr_get(x_29, 0);
lean::dec(x_48);
x_49 = lean::nat_sub(x_23, x_42);
lean::dec(x_23);
x_50 = lean::box(13);
lean::cnstr_set_tag(x_29, 6);
lean::cnstr_set(x_29, 2, x_50);
lean::cnstr_set(x_29, 1, x_49);
lean::cnstr_set(x_29, 0, x_22);
lean::cnstr_set_scalar(x_29, sizeof(void*)*3, x_24);
x_51 = lean::array_push(x_44, x_29);
x_2 = x_39;
x_3 = x_41;
x_4 = x_51;
goto _start;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_29);
x_53 = lean::nat_sub(x_23, x_42);
lean::dec(x_23);
x_54 = lean::box(13);
x_55 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_55, 0, x_22);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*3, x_24);
x_56 = lean::array_push(x_44, x_55);
x_2 = x_39;
x_3 = x_41;
x_4 = x_56;
goto _start;
}
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_23);
lean::dec(x_22);
x_58 = lean::array_push(x_4, x_29);
x_2 = x_39;
x_3 = x_41;
x_4 = x_58;
goto _start;
}
}
}
}
else
{
obj* x_60; 
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_23);
lean::dec(x_22);
x_60 = lean::box(0);
x_5 = x_60;
goto block_10;
}
}
else
{
obj* x_61; 
lean::dec(x_29);
lean::dec(x_23);
lean::dec(x_22);
x_61 = lean::box(0);
x_5 = x_61;
goto block_10;
}
}
else
{
obj* x_62; 
lean::dec(x_23);
lean::dec(x_22);
lean::dec(x_16);
x_62 = lean::box(0);
x_5 = x_62;
goto block_10;
}
}
default: 
{
obj* x_63; 
lean::dec(x_19);
lean::dec(x_16);
x_63 = lean::box(0);
x_5 = x_63;
goto block_10;
}
}
}
else
{
obj* x_64; 
lean::dec(x_16);
x_64 = lean::box(0);
x_5 = x_64;
goto block_10;
}
block_10:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_5);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_reverseAux___main___rarg(x_4, x_6);
x_8 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_7, x_7, x_6, x_2);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
block_15:
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::array_pop(x_2);
x_13 = lean::array_push(x_4, x_11);
x_2 = x_12;
x_4 = x_13;
goto _start;
}
}
}
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = lean::mk_array(x_1, x_4);
x_6 = l_Array_empty___closed__1;
x_7 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_2, x_3, x_5, x_6);
return x_7;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_3, x_2);
x_9 = lean::box(0);
lean::inc(x_8);
x_10 = x_9;
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
x_16 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
x_18 = x_17;
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
x_22 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = x_23;
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 2)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_2);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = lean::cnstr_get(x_2, 2);
x_14 = lean::cnstr_get(x_2, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_11, 2);
lean::inc(x_17);
x_18 = lean::nat_dec_eq(x_1, x_15);
lean::dec(x_15);
if (x_18 == 0)
{
obj* x_19; 
lean::dec(x_17);
lean::dec(x_16);
x_19 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_13);
lean::cnstr_set(x_2, 2, x_19);
return x_2;
}
else
{
obj* x_20; 
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_2, 1, x_20);
return x_2;
}
}
else
{
obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
x_21 = lean::cnstr_get(x_2, 0);
x_22 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_23);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_11, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_11, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_11, 2);
lean::inc(x_26);
x_27 = lean::nat_dec_eq(x_1, x_24);
lean::dec(x_24);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_26);
lean::dec(x_25);
x_28 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_23);
x_29 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*3, x_22);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_11);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_26);
x_31 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_31, 0, x_21);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set(x_31, 2, x_23);
lean::cnstr_set_scalar(x_31, sizeof(void*)*3, x_22);
return x_31;
}
}
}
else
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_2);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_2, 2);
x_34 = lean::cnstr_get(x_2, 1);
lean::dec(x_34);
x_35 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_33);
lean::cnstr_set(x_2, 2, x_35);
return x_2;
}
else
{
obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_2, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_38 = lean::cnstr_get(x_2, 2);
lean::inc(x_38);
lean::inc(x_36);
lean::dec(x_2);
x_39 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_38);
x_40 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_11);
lean::cnstr_set(x_40, 2, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*3, x_37);
return x_40;
}
}
}
case 7:
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_2);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; uint8 x_45; 
x_42 = lean::cnstr_get(x_2, 0);
x_43 = lean::cnstr_get(x_2, 1);
x_44 = lean::cnstr_get(x_2, 2);
x_45 = lean::nat_dec_eq(x_1, x_42);
if (x_45 == 0)
{
obj* x_46; 
x_46 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_44);
lean::cnstr_set(x_2, 2, x_46);
return x_2;
}
else
{
lean::free_heap_obj(x_2);
lean::dec(x_43);
lean::dec(x_42);
return x_44;
}
}
else
{
obj* x_47; obj* x_48; uint8 x_49; obj* x_50; uint8 x_51; 
x_47 = lean::cnstr_get(x_2, 0);
x_48 = lean::cnstr_get(x_2, 1);
x_49 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_50 = lean::cnstr_get(x_2, 2);
lean::inc(x_50);
lean::inc(x_48);
lean::inc(x_47);
lean::dec(x_2);
x_51 = lean::nat_dec_eq(x_1, x_47);
if (x_51 == 0)
{
obj* x_52; obj* x_53; 
x_52 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_50);
x_53 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_53, 0, x_47);
lean::cnstr_set(x_53, 1, x_48);
lean::cnstr_set(x_53, 2, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*3, x_49);
return x_53;
}
else
{
lean::dec(x_48);
lean::dec(x_47);
return x_50;
}
}
}
case 10:
{
uint8 x_54; 
x_54 = !lean::is_exclusive(x_2);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_2, 2);
x_56 = lean::mk_nat_obj(0u);
x_57 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_1, x_56, x_55);
lean::cnstr_set(x_2, 2, x_57);
return x_2;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_58 = lean::cnstr_get(x_2, 0);
x_59 = lean::cnstr_get(x_2, 1);
x_60 = lean::cnstr_get(x_2, 2);
lean::inc(x_60);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_2);
x_61 = lean::mk_nat_obj(0u);
x_62 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_1, x_61, x_60);
x_63 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_63, 0, x_58);
lean::cnstr_set(x_63, 1, x_59);
lean::cnstr_set(x_63, 2, x_62);
return x_63;
}
}
default: 
{
obj* x_64; 
x_64 = lean::box(0);
x_3 = x_64;
goto block_10;
}
}
block_10:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = l_Lean_IR_FnBody_body___main(x_2);
x_6 = lean::box(13);
x_7 = l_Lean_IR_FnBody_setBody___main(x_2, x_6);
x_8 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_5);
x_9 = l_Lean_IR_FnBody_setBody___main(x_7, x_8);
return x_9;
}
else
{
return x_2;
}
}
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_3, x_8);
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; 
lean::dec(x_7);
x_3 = x_9;
goto _start;
}
else
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_12 = 1;
x_13 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_8);
lean::cnstr_set(x_13, 2, x_4);
lean::cnstr_set_scalar(x_13, sizeof(void*)*3, x_12);
x_3 = x_9;
x_4 = x_13;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_mkSlowPath(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = 1;
x_8 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*3, x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_3, x_3, x_9, x_8);
return x_10;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFresh(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExpandResetReuse_mkFresh___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_mkFresh(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_4, x_10);
lean::dec(x_4);
x_12 = lean::nat_sub(x_3, x_11);
x_13 = lean::nat_sub(x_12, x_10);
lean::dec(x_12);
x_14 = lean::box(0);
x_15 = lean::array_get(x_14, x_2, x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; 
lean::dec(x_15);
x_16 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_7);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
lean::dec(x_16);
lean::inc(x_1);
x_19 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_19, 0, x_13);
lean::cnstr_set(x_19, 1, x_1);
x_20 = 1;
lean::inc(x_17);
x_21 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_10);
lean::cnstr_set(x_21, 2, x_5);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_20);
x_22 = 7;
x_23 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*3, x_22);
x_4 = x_11;
x_5 = x_23;
x_7 = x_18;
goto _start;
}
else
{
obj* x_25; 
lean::dec(x_15);
lean::dec(x_13);
x_4 = x_11;
goto _start;
}
}
else
{
obj* x_26; 
lean::dec(x_4);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_7);
return x_26;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::array_get_size(x_2);
lean::inc(x_6);
x_7 = l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_6, x_6, x_3, x_4, x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
x_10 = lean::nat_sub(x_3, x_4);
lean::dec(x_4);
x_11 = l_Lean_IR_Arg_Inhabited;
x_12 = lean::array_get(x_11, x_2, x_10);
lean::inc(x_1);
x_13 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_12);
lean::cnstr_set(x_13, 3, x_5);
x_4 = x_9;
x_5 = x_13;
goto _start;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_setFields(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::array_get_size(x_2);
lean::inc(x_4);
x_5 = l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_4, x_4, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_IR_ExpandResetReuse_setFields___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_setFields(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean::nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
obj* x_8; 
x_2 = x_6;
goto _start;
}
else
{
obj* x_9; 
lean::inc(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_5);
return x_9;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean::usize_of_nat(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
uint8 l_Lean_IR_ExpandResetReuse_isSelfSet(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
lean::dec(x_6);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 3)
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::nat_dec_eq(x_9, x_3);
lean::dec(x_9);
if (x_11 == 0)
{
uint8 x_12; 
lean::dec(x_10);
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = lean::nat_dec_eq(x_10, x_2);
lean::dec(x_10);
return x_13;
}
}
else
{
uint8 x_14; 
lean::dec(x_8);
x_14 = 0;
return x_14;
}
}
}
else
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
}
}
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_Lean_IR_ExpandResetReuse_isSelfUSet(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_5);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
if (lean::obj_tag(x_7) == 4)
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::nat_dec_eq(x_8, x_3);
lean::dec(x_8);
if (x_10 == 0)
{
uint8 x_11; 
lean::dec(x_9);
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = lean::nat_dec_eq(x_9, x_2);
lean::dec(x_9);
return x_12;
}
}
else
{
uint8 x_13; 
lean::dec(x_7);
x_13 = 0;
return x_13;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_Lean_IR_ExpandResetReuse_isSelfSSet(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
lean::dec(x_6);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 5)
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
lean::dec(x_8);
x_12 = lean::nat_dec_eq(x_3, x_9);
lean::dec(x_9);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_11);
lean::dec(x_10);
x_13 = 0;
return x_13;
}
else
{
uint8 x_14; 
x_14 = lean::nat_dec_eq(x_10, x_4);
lean::dec(x_10);
if (x_14 == 0)
{
uint8 x_15; 
lean::dec(x_11);
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::nat_dec_eq(x_11, x_2);
lean::dec(x_11);
return x_16;
}
}
}
else
{
uint8 x_17; 
lean::dec(x_8);
x_17 = 0;
return x_17;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_3, x_2);
x_9 = lean::box(0);
lean::inc(x_8);
x_10 = x_9;
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
x_16 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
x_18 = x_17;
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
x_22 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = x_23;
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_2)) {
case 2:
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_12 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_2, 1);
x_14 = lean::cnstr_get(x_2, 2);
x_15 = lean::cnstr_get(x_2, 3);
x_16 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_12, x_13, x_14);
if (x_16 == 0)
{
obj* x_17; 
x_17 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_15);
lean::cnstr_set(x_2, 3, x_17);
return x_2;
}
else
{
obj* x_18; 
lean::free_heap_obj(x_2);
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_12);
x_2 = x_15;
goto _start;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_2, 0);
x_20 = lean::cnstr_get(x_2, 1);
x_21 = lean::cnstr_get(x_2, 2);
x_22 = lean::cnstr_get(x_2, 3);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_2);
x_23 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_19, x_20, x_21);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_22);
x_25 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_20);
lean::cnstr_set(x_25, 2, x_21);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
else
{
obj* x_26; 
lean::dec(x_21);
lean::dec(x_20);
lean::dec(x_19);
x_2 = x_22;
goto _start;
}
}
}
case 4:
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_2);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_2, 0);
x_29 = lean::cnstr_get(x_2, 1);
x_30 = lean::cnstr_get(x_2, 2);
x_31 = lean::cnstr_get(x_2, 3);
x_32 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_28, x_29, x_30);
if (x_32 == 0)
{
obj* x_33; 
x_33 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_31);
lean::cnstr_set(x_2, 3, x_33);
return x_2;
}
else
{
obj* x_34; 
lean::free_heap_obj(x_2);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
x_2 = x_31;
goto _start;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint8 x_39; 
x_35 = lean::cnstr_get(x_2, 0);
x_36 = lean::cnstr_get(x_2, 1);
x_37 = lean::cnstr_get(x_2, 2);
x_38 = lean::cnstr_get(x_2, 3);
lean::inc(x_38);
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_2);
x_39 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_35, x_36, x_37);
if (x_39 == 0)
{
obj* x_40; obj* x_41; 
x_40 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_38);
x_41 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_41, 0, x_35);
lean::cnstr_set(x_41, 1, x_36);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_40);
return x_41;
}
else
{
obj* x_42; 
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_35);
x_2 = x_38;
goto _start;
}
}
}
case 5:
{
uint8 x_43; 
x_43 = !lean::is_exclusive(x_2);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; 
x_44 = lean::cnstr_get(x_2, 0);
x_45 = lean::cnstr_get(x_2, 1);
x_46 = lean::cnstr_get(x_2, 2);
x_47 = lean::cnstr_get(x_2, 3);
x_48 = lean::cnstr_get(x_2, 4);
x_49 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_44, x_45, x_46, x_47);
if (x_49 == 0)
{
obj* x_50; 
x_50 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_48);
lean::cnstr_set(x_2, 4, x_50);
return x_2;
}
else
{
obj* x_51; 
lean::free_heap_obj(x_2);
lean::dec(x_47);
lean::dec(x_46);
lean::dec(x_45);
lean::dec(x_44);
x_2 = x_48;
goto _start;
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint8 x_56; obj* x_57; uint8 x_58; 
x_52 = lean::cnstr_get(x_2, 0);
x_53 = lean::cnstr_get(x_2, 1);
x_54 = lean::cnstr_get(x_2, 2);
x_55 = lean::cnstr_get(x_2, 3);
x_56 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_57 = lean::cnstr_get(x_2, 4);
lean::inc(x_57);
lean::inc(x_55);
lean::inc(x_54);
lean::inc(x_53);
lean::inc(x_52);
lean::dec(x_2);
x_58 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_52, x_53, x_54, x_55);
if (x_58 == 0)
{
obj* x_59; obj* x_60; 
x_59 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_57);
x_60 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_60, 0, x_52);
lean::cnstr_set(x_60, 1, x_53);
lean::cnstr_set(x_60, 2, x_54);
lean::cnstr_set(x_60, 3, x_55);
lean::cnstr_set(x_60, 4, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*5, x_56);
return x_60;
}
else
{
obj* x_61; 
lean::dec(x_55);
lean::dec(x_54);
lean::dec(x_53);
lean::dec(x_52);
x_2 = x_57;
goto _start;
}
}
}
case 10:
{
uint8 x_62; 
x_62 = !lean::is_exclusive(x_2);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = lean::cnstr_get(x_2, 2);
x_64 = lean::mk_nat_obj(0u);
x_65 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_1, x_64, x_63);
lean::cnstr_set(x_2, 2, x_65);
return x_2;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_2, 0);
x_67 = lean::cnstr_get(x_2, 1);
x_68 = lean::cnstr_get(x_2, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_2);
x_69 = lean::mk_nat_obj(0u);
x_70 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_1, x_69, x_68);
x_71 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_71, 0, x_66);
lean::cnstr_set(x_71, 1, x_67);
lean::cnstr_set(x_71, 2, x_70);
return x_71;
}
}
default: 
{
obj* x_72; 
x_72 = lean::box(0);
x_3 = x_72;
goto block_10;
}
}
block_10:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = l_Lean_IR_FnBody_body___main(x_2);
x_6 = lean::box(13);
x_7 = l_Lean_IR_FnBody_setBody___main(x_2, x_6);
x_8 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_5);
x_9 = l_Lean_IR_FnBody_setBody___main(x_7, x_8);
return x_9;
}
else
{
return x_2;
}
}
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_4);
lean::dec(x_3);
x_8 = l_Array_empty___closed__1;
x_9 = x_5;
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::array_fget(x_5, x_4);
x_11 = lean::box(0);
lean::inc(x_10);
x_12 = x_11;
x_13 = lean::array_fset(x_5, x_4, x_12);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
if (lean::obj_tag(x_10) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
lean::inc(x_3);
x_18 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = x_19;
x_21 = lean::array_fset(x_13, x_4, x_20);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_21;
goto _start;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_10, 0);
lean::inc(x_23);
lean::inc(x_3);
x_24 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = x_25;
x_27 = lean::array_fset(x_13, x_4, x_26);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_4, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 2)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_4);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; uint8 x_22; 
x_15 = lean::cnstr_get(x_4, 0);
x_16 = lean::cnstr_get(x_4, 2);
x_17 = lean::cnstr_get(x_4, 1);
lean::dec(x_17);
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
x_20 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*3);
x_21 = lean::cnstr_get(x_13, 2);
lean::inc(x_21);
x_22 = lean::nat_dec_eq(x_2, x_18);
lean::dec(x_18);
if (x_22 == 0)
{
obj* x_23; 
lean::dec(x_21);
lean::dec(x_19);
x_23 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_16);
lean::cnstr_set(x_4, 2, x_23);
return x_4;
}
else
{
obj* x_24; obj* x_25; 
lean::free_heap_obj(x_4);
lean::dec(x_13);
lean::inc(x_3);
x_24 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_15, x_3, x_16);
lean::dec(x_15);
lean::inc(x_3);
x_25 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_21, x_24);
lean::dec(x_21);
if (x_20 == 0)
{
obj* x_26; 
lean::dec(x_19);
lean::dec(x_3);
x_26 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_19, 1);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_28, 0, x_3);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set(x_28, 2, x_25);
x_29 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_28);
return x_29;
}
}
}
else
{
obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; uint8 x_37; 
x_30 = lean::cnstr_get(x_4, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*3);
x_32 = lean::cnstr_get(x_4, 2);
lean::inc(x_32);
lean::inc(x_30);
lean::dec(x_4);
x_33 = lean::cnstr_get(x_13, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_13, 1);
lean::inc(x_34);
x_35 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*3);
x_36 = lean::cnstr_get(x_13, 2);
lean::inc(x_36);
x_37 = lean::nat_dec_eq(x_2, x_33);
lean::dec(x_33);
if (x_37 == 0)
{
obj* x_38; obj* x_39; 
lean::dec(x_36);
lean::dec(x_34);
x_38 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_32);
x_39 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_39, 0, x_30);
lean::cnstr_set(x_39, 1, x_13);
lean::cnstr_set(x_39, 2, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*3, x_31);
return x_39;
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_13);
lean::inc(x_3);
x_40 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_30, x_3, x_32);
lean::dec(x_30);
lean::inc(x_3);
x_41 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_36, x_40);
lean::dec(x_36);
if (x_35 == 0)
{
obj* x_42; 
lean::dec(x_34);
lean::dec(x_3);
x_42 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_41);
return x_42;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_34, 1);
lean::inc(x_43);
lean::dec(x_34);
x_44 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_44, 0, x_3);
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set(x_44, 2, x_41);
x_45 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_44);
return x_45;
}
}
}
}
else
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_4);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_4, 2);
x_48 = lean::cnstr_get(x_4, 1);
lean::dec(x_48);
x_49 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_47);
lean::cnstr_set(x_4, 2, x_49);
return x_4;
}
else
{
obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_4, 0);
x_51 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*3);
x_52 = lean::cnstr_get(x_4, 2);
lean::inc(x_52);
lean::inc(x_50);
lean::dec(x_4);
x_53 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_52);
x_54 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_13);
lean::cnstr_set(x_54, 2, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*3, x_51);
return x_54;
}
}
}
case 7:
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_4);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; uint8 x_59; 
x_56 = lean::cnstr_get(x_4, 0);
x_57 = lean::cnstr_get(x_4, 1);
x_58 = lean::cnstr_get(x_4, 2);
x_59 = lean::nat_dec_eq(x_2, x_56);
if (x_59 == 0)
{
obj* x_60; 
x_60 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_58);
lean::cnstr_set(x_4, 2, x_60);
return x_4;
}
else
{
obj* x_61; 
lean::free_heap_obj(x_4);
lean::dec(x_57);
lean::dec(x_56);
x_61 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_61, 0, x_3);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
}
else
{
obj* x_62; obj* x_63; uint8 x_64; obj* x_65; uint8 x_66; 
x_62 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get(x_4, 1);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*3);
x_65 = lean::cnstr_get(x_4, 2);
lean::inc(x_65);
lean::inc(x_63);
lean::inc(x_62);
lean::dec(x_4);
x_66 = lean::nat_dec_eq(x_2, x_62);
if (x_66 == 0)
{
obj* x_67; obj* x_68; 
x_67 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_65);
x_68 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_68, 0, x_62);
lean::cnstr_set(x_68, 1, x_63);
lean::cnstr_set(x_68, 2, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*3, x_64);
return x_68;
}
else
{
obj* x_69; 
lean::dec(x_63);
lean::dec(x_62);
x_69 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_69, 0, x_3);
lean::cnstr_set(x_69, 1, x_65);
return x_69;
}
}
}
case 10:
{
uint8 x_70; 
x_70 = !lean::is_exclusive(x_4);
if (x_70 == 0)
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_4, 2);
x_72 = lean::mk_nat_obj(0u);
x_73 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_1, x_2, x_3, x_72, x_71);
lean::cnstr_set(x_4, 2, x_73);
return x_4;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_4, 0);
x_75 = lean::cnstr_get(x_4, 1);
x_76 = lean::cnstr_get(x_4, 2);
lean::inc(x_76);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_4);
x_77 = lean::mk_nat_obj(0u);
x_78 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_1, x_2, x_3, x_77, x_76);
x_79 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_79, 0, x_74);
lean::cnstr_set(x_79, 1, x_75);
lean::cnstr_set(x_79, 2, x_78);
return x_79;
}
}
default: 
{
obj* x_80; 
x_80 = lean::box(0);
x_5 = x_80;
goto block_12;
}
}
block_12:
{
uint8 x_6; 
lean::dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal___main(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = l_Lean_IR_FnBody_body___main(x_4);
x_8 = lean::box(13);
x_9 = l_Lean_IR_FnBody_setBody___main(x_4, x_8);
x_10 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_7);
x_11 = l_Lean_IR_FnBody_setBody___main(x_9, x_10);
return x_11;
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFastPath(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_2);
x_7 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_5, x_1, x_2, x_4);
x_8 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_IR_ExpandResetReuse_expand(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_9 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_4, x_5, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
lean::inc(x_6);
lean::inc(x_5);
x_12 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean::inc(x_5);
x_13 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_3, x_5, x_11, x_6, x_7, x_8);
lean::dec(x_11);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::dec(x_13);
x_16 = l_Array_empty___closed__1;
x_17 = lean::apply_4(x_1, x_14, x_16, x_7, x_15);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
lean::dec(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_19);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::inc(x_22);
x_24 = l_Lean_IR_mkIf(x_22, x_12, x_18);
x_25 = 1;
x_26 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*3, x_25);
x_27 = l_Lean_IR_reshape(x_10, x_26);
lean::cnstr_set(x_20, 0, x_27);
return x_20;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_20, 0);
x_29 = lean::cnstr_get(x_20, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_20);
x_30 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::inc(x_28);
x_31 = l_Lean_IR_mkIf(x_28, x_12, x_18);
x_32 = 1;
x_33 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set(x_33, 1, x_30);
lean::cnstr_set(x_33, 2, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*3, x_32);
x_34 = l_Lean_IR_reshape(x_10, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_29);
return x_35;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_expand___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_expand(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_3);
return x_9;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::array_fget(x_2, x_1);
x_11 = lean::box(0);
lean::inc(x_10);
x_12 = x_11;
x_13 = lean::array_fset(x_2, x_1, x_12);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
x_16 = l_Array_empty___closed__1;
lean::inc(x_3);
x_17 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_15, x_16, x_3, x_4);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
lean::dec(x_17);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_14);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_1, x_21);
x_23 = x_20;
x_24 = lean::array_fset(x_13, x_1, x_23);
lean::dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_4 = x_19;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_26 = lean::cnstr_get(x_10, 0);
lean::inc(x_26);
x_27 = l_Array_empty___closed__1;
lean::inc(x_3);
x_28 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_26, x_27, x_3, x_4);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_29);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::nat_add(x_1, x_32);
x_34 = x_31;
x_35 = lean::array_fset(x_13, x_1, x_34);
lean::dec(x_1);
x_1 = x_33;
x_2 = x_35;
x_4 = x_30;
goto _start;
}
}
}
}
obj* _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExpandResetReuse_searchAndExpand___main), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 1)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_1, 2);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_13, 1);
lean::inc(x_17);
lean::dec(x_13);
lean::inc(x_15);
x_18 = l_Lean_IR_ExpandResetReuse_consumed___main(x_14, x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_17);
lean::dec(x_16);
lean::dec(x_14);
x_19 = l_Lean_IR_push(x_2, x_1);
x_1 = x_15;
x_2 = x_19;
goto _start;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_1);
x_21 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1;
x_22 = l_Lean_IR_ExpandResetReuse_expand(x_21, x_2, x_14, x_16, x_17, x_15, x_3, x_4);
lean::dec(x_14);
return x_22;
}
}
else
{
obj* x_23; 
lean::dec(x_13);
x_23 = lean::box(0);
x_5 = x_23;
goto block_12;
}
}
case 1:
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_1);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_1, 2);
x_26 = lean::cnstr_get(x_1, 3);
x_27 = l_Array_empty___closed__1;
lean::inc(x_3);
x_28 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_25, x_27, x_3, x_4);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_31 = lean::box(13);
lean::cnstr_set(x_1, 3, x_31);
lean::cnstr_set(x_1, 2, x_29);
x_32 = l_Lean_IR_push(x_2, x_1);
x_1 = x_26;
x_2 = x_32;
x_4 = x_30;
goto _start;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_34 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get(x_1, 1);
x_36 = lean::cnstr_get(x_1, 2);
x_37 = lean::cnstr_get(x_1, 3);
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_1);
x_38 = l_Array_empty___closed__1;
lean::inc(x_3);
x_39 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_36, x_38, x_3, x_4);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_39, 1);
lean::inc(x_41);
lean::dec(x_39);
x_42 = lean::box(13);
x_43 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_43, 0, x_34);
lean::cnstr_set(x_43, 1, x_35);
lean::cnstr_set(x_43, 2, x_40);
lean::cnstr_set(x_43, 3, x_42);
x_44 = l_Lean_IR_push(x_2, x_43);
x_1 = x_37;
x_2 = x_44;
x_4 = x_41;
goto _start;
}
}
case 10:
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_1);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; uint8 x_50; 
x_47 = lean::cnstr_get(x_1, 2);
x_48 = lean::mk_nat_obj(0u);
x_49 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(x_48, x_47, x_3, x_4);
x_50 = !lean::is_exclusive(x_49);
if (x_50 == 0)
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_49, 0);
lean::cnstr_set(x_1, 2, x_51);
x_52 = l_Lean_IR_reshape(x_2, x_1);
lean::cnstr_set(x_49, 0, x_52);
return x_49;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_53 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_49);
lean::cnstr_set(x_1, 2, x_53);
x_55 = l_Lean_IR_reshape(x_2, x_1);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_54);
return x_56;
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_57 = lean::cnstr_get(x_1, 0);
x_58 = lean::cnstr_get(x_1, 1);
x_59 = lean::cnstr_get(x_1, 2);
lean::inc(x_59);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_1);
x_60 = lean::mk_nat_obj(0u);
x_61 = l_Array_ummapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(x_60, x_59, x_3, x_4);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_61, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_64 = x_61;
} else {
 lean::dec_ref(x_61);
 x_64 = lean::box(0);
}
x_65 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_65, 0, x_57);
lean::cnstr_set(x_65, 1, x_58);
lean::cnstr_set(x_65, 2, x_62);
x_66 = l_Lean_IR_reshape(x_2, x_65);
if (lean::is_scalar(x_64)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_64;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_63);
return x_67;
}
}
default: 
{
obj* x_68; 
x_68 = lean::box(0);
x_5 = x_68;
goto block_12;
}
}
block_12:
{
uint8 x_6; 
lean::dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_IR_FnBody_body___main(x_1);
x_8 = l_Lean_IR_push(x_2, x_1);
x_1 = x_7;
x_2 = x_8;
goto _start;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_3);
x_10 = l_Lean_IR_reshape(x_2, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Decl_normalizeIds(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
lean::inc(x_2);
x_7 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_2);
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_9 = l_Lean_IR_MaxIndex_collectDecl___main(x_2, x_8);
x_10 = !lean::is_exclusive(x_2);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_2, 2);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_2, 1);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_2, 0);
lean::dec(x_13);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_9, x_14);
lean::dec(x_9);
x_16 = l_Array_empty___closed__1;
x_17 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_6, x_16, x_7, x_15);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
lean::dec(x_17);
lean::cnstr_set(x_2, 2, x_18);
return x_2;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_2);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_9, x_19);
lean::dec(x_9);
x_21 = l_Array_empty___closed__1;
x_22 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_6, x_21, x_7, x_20);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_24 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_24, 0, x_3);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*3, x_5);
return x_24;
}
}
else
{
return x_2;
}
}
}
obj* l_Lean_IR_Decl_expandResetReuse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_main(x_1);
return x_2;
}
}
obj* initialize_init_control_state(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
obj* initialize_init_lean_compiler_ir_freevars(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_expandresetreuse(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (io_result_is_error(w)) return w;
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1();
lean::mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1);
l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1 = _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1();
lean::mark_persistent(l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1);
return w;
}
