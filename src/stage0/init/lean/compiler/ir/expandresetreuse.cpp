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
obj* l_Lean_IR_Decl_expandResetReuse(obj*);
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(obj*, obj*);
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
uint8 l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(obj*, obj*);
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_expand(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1___boxed(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkFresh(obj*);
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
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_IR_mkIf(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(obj*, obj*);
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
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(obj*, obj*, obj*);
obj* l_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
uint8 l_Lean_IR_ExpandResetReuse_isSelfSet(obj*, obj*, obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(obj*, obj*, obj*);
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_expand___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main___boxed(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
extern obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
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
obj* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
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
uint8 l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::nat_dec_eq(x_3, x_0);
if (x_5 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; usize x_10; usize x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::array_get_size(x_0);
x_10 = lean::usize_of_nat(x_2);
x_11 = lean::usize_modn(x_10, x_9);
lean::dec(x_9);
x_13 = lean::array_uget(x_0, x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::array_uset(x_0, x_11, x_14);
x_0 = x_15;
x_1 = x_6;
goto _start;
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_0);
x_9 = lean::box(0);
x_10 = lean::array_fset(x_1, x_0, x_9);
x_11 = l_AssocList_foldl___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(x_2, x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_0, x_12);
lean::dec(x_0);
x_0 = x_13;
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(2ul);
x_4 = lean::nat_mul(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_4, x_6);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(x_8, x_1, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::nat_dec_eq(x_5, x_0);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_0, x_1, x_9);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
else
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_5);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set(x_17, 2, x_9);
return x_17;
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::array_get_size(x_5);
x_9 = lean::usize_of_nat(x_1);
x_10 = lean::usize_modn(x_9, x_8);
x_11 = lean::array_uget(x_5, x_10);
x_12 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_1, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_11);
x_17 = lean::array_uset(x_5, x_10, x_16);
x_18 = lean::nat_dec_le(x_14, x_8);
lean::dec(x_8);
if (x_18 == 0)
{
obj* x_21; 
lean::dec(x_7);
x_21 = l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_14, x_17);
return x_21;
}
else
{
obj* x_22; 
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_8);
x_24 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_11);
x_25 = lean::array_uset(x_5, x_10, x_24);
if (lean::is_scalar(x_7)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_7;
}
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 3:
{
obj* x_3; 
x_3 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_2, x_0, x_1);
return x_3;
}
case 4:
{
obj* x_4; 
x_4 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_2, x_0, x_1);
return x_4;
}
case 5:
{
obj* x_5; 
x_5 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_2, x_0, x_1);
return x_5;
}
default:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_11 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_9, x_3);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_11;
goto _start;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_8, x_1);
switch (lean::obj_tag(x_6)) {
case 3:
{
obj* x_12; 
x_12 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_11, x_4, x_6);
return x_12;
}
case 4:
{
obj* x_13; 
x_13 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_11, x_4, x_6);
return x_13;
}
case 5:
{
obj* x_14; 
x_14 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_11, x_4, x_6);
return x_14;
}
default:
{
lean::dec(x_6);
lean::dec(x_4);
return x_11;
}
}
}
case 1:
{
obj* x_17; obj* x_19; obj* x_22; 
x_17 = lean::cnstr_get(x_0, 2);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 3);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_19, x_1);
x_0 = x_17;
x_1 = x_22;
goto _start;
}
case 10:
{
obj* x_24; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_0, 2);
lean::inc(x_24);
lean::dec(x_0);
x_27 = lean::mk_nat_obj(0ul);
x_28 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(x_24, x_24, x_27, x_1);
lean::dec(x_24);
return x_28;
}
default:
{
obj* x_30; 
x_30 = lean::box(0);
x_2 = x_30;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_32; 
lean::dec(x_2);
x_32 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_32 == 0)
{
obj* x_33; 
x_33 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_33;
goto _start;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(8ul);
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkProjMap(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 2);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
x_5 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_1, x_4);
return x_5;
}
else
{
obj* x_7; 
lean::dec(x_0);
x_7 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
return x_7;
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_11 = l_Lean_IR_ExpandResetReuse_consumed___main(x_0, x_9);
if (x_11 == 0)
{
uint8 x_13; 
lean::dec(x_2);
x_13 = 1;
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_2, x_14);
lean::dec(x_2);
x_2 = x_15;
goto _start;
}
}
}
}
uint8 l_Lean_IR_ExpandResetReuse_consumed___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
switch (lean::obj_tag(x_4)) {
case 2:
{
obj* x_6; obj* x_9; uint8 x_12; 
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::nat_dec_eq(x_0, x_9);
lean::dec(x_9);
if (x_12 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
uint8 x_16; 
lean::dec(x_6);
x_16 = 1;
return x_16;
}
}
default:
{
obj* x_18; 
lean::dec(x_4);
x_18 = lean::cnstr_get(x_1, 2);
lean::inc(x_18);
lean::dec(x_1);
x_1 = x_18;
goto _start;
}
}
}
case 7:
{
obj* x_22; obj* x_24; uint8 x_27; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_1, 2);
lean::inc(x_24);
lean::dec(x_1);
x_27 = lean::nat_dec_eq(x_0, x_22);
lean::dec(x_22);
if (x_27 == 0)
{
x_1 = x_24;
goto _start;
}
else
{
uint8 x_31; 
lean::dec(x_24);
x_31 = 1;
return x_31;
}
}
case 10:
{
obj* x_32; obj* x_35; uint8 x_36; 
x_32 = lean::cnstr_get(x_1, 2);
lean::inc(x_32);
lean::dec(x_1);
x_35 = lean::mk_nat_obj(0ul);
x_36 = l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_0, x_32, x_35);
lean::dec(x_32);
if (x_36 == 0)
{
uint8 x_38; 
x_38 = 1;
return x_38;
}
else
{
uint8 x_39; 
x_39 = 0;
return x_39;
}
}
default:
{
obj* x_40; 
x_40 = lean::box(0);
x_2 = x_40;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_42; 
lean::dec(x_2);
x_42 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_42 == 0)
{
obj* x_43; 
x_43 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_43;
goto _start;
}
else
{
uint8 x_47; 
lean::dec(x_1);
x_47 = 0;
return x_47;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_consumed___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_Lean_IR_ExpandResetReuse_consumed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_consumed___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_consumed___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_consumed(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_sub(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean::array_get(x_5, x_0, x_3);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::array_get_size(x_1);
x_9 = lean::mk_nat_obj(2ul);
x_10 = lean::nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
obj* x_11; 
x_11 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(x_1);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_13; 
lean::dec(x_8);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
switch (lean::obj_tag(x_13)) {
case 4:
{
lean::dec(x_13);
x_6 = x_11;
goto lbl_7;
}
case 5:
{
lean::dec(x_13);
x_6 = x_11;
goto lbl_7;
}
default:
{
obj* x_19; 
lean::dec(x_11);
lean::dec(x_13);
x_19 = lean::box(0);
x_4 = x_19;
goto lbl_5;
}
}
}
case 6:
{
obj* x_20; obj* x_22; uint8 x_24; obj* x_26; uint8 x_27; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*3);
lean::dec(x_11);
x_26 = lean::mk_nat_obj(0ul);
x_27 = lean::nat_dec_eq(x_22, x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_30; obj* x_31; 
x_28 = lean::nat_sub(x_8, x_9);
lean::dec(x_8);
x_30 = l_Lean_IR_Inhabited;
x_31 = lean::array_get(x_30, x_1, x_28);
lean::dec(x_28);
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_33; 
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
switch (lean::obj_tag(x_33)) {
case 3:
{
obj* x_35; obj* x_37; obj* x_39; uint8 x_42; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_33, 1);
lean::inc(x_39);
lean::dec(x_33);
x_42 = lean::nat_dec_eq(x_35, x_20);
lean::dec(x_35);
if (x_42 == 0)
{
obj* x_49; 
lean::dec(x_39);
lean::dec(x_22);
lean::dec(x_31);
lean::dec(x_20);
lean::dec(x_37);
x_49 = lean::box(0);
x_4 = x_49;
goto lbl_5;
}
else
{
uint8 x_50; 
x_50 = lean::nat_dec_eq(x_0, x_39);
lean::dec(x_39);
if (x_50 == 0)
{
obj* x_56; 
lean::dec(x_22);
lean::dec(x_31);
lean::dec(x_20);
lean::dec(x_37);
x_56 = lean::box(0);
x_4 = x_56;
goto lbl_5;
}
else
{
obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_63; uint8 x_64; 
x_57 = lean::array_pop(x_1);
x_58 = lean::array_pop(x_57);
lean::inc(x_20);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_20);
x_61 = lean::array_set(x_2, x_37, x_60);
lean::dec(x_37);
x_63 = lean::mk_nat_obj(1ul);
x_64 = lean::nat_dec_eq(x_22, x_63);
if (x_64 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::inc(x_31);
x_66 = lean::array_push(x_3, x_31);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 lean::cnstr_release(x_31, 2);
 x_67 = x_31;
} else {
 lean::dec(x_31);
 x_67 = lean::box(0);
}
x_68 = lean::nat_sub(x_22, x_63);
lean::dec(x_22);
x_70 = lean::box(13);
if (lean::is_scalar(x_67)) {
 x_71 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_71 = x_67;
 lean::cnstr_set_tag(x_67, 6);
}
lean::cnstr_set(x_71, 0, x_20);
lean::cnstr_set(x_71, 1, x_68);
lean::cnstr_set(x_71, 2, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*3, x_24);
x_72 = x_71;
x_73 = lean::array_push(x_66, x_72);
x_1 = x_58;
x_2 = x_61;
x_3 = x_73;
goto _start;
}
else
{
obj* x_77; 
lean::dec(x_22);
lean::dec(x_20);
x_77 = lean::array_push(x_3, x_31);
x_1 = x_58;
x_2 = x_61;
x_3 = x_77;
goto _start;
}
}
}
}
default:
{
obj* x_83; 
lean::dec(x_22);
lean::dec(x_31);
lean::dec(x_33);
lean::dec(x_20);
x_83 = lean::box(0);
x_4 = x_83;
goto lbl_5;
}
}
}
case 13:
{
obj* x_86; 
lean::dec(x_22);
lean::dec(x_20);
x_86 = lean::box(0);
x_4 = x_86;
goto lbl_5;
}
default:
{
obj* x_90; 
lean::dec(x_22);
lean::dec(x_31);
lean::dec(x_20);
x_90 = lean::box(0);
x_4 = x_90;
goto lbl_5;
}
}
}
else
{
obj* x_94; 
lean::dec(x_8);
lean::dec(x_22);
lean::dec(x_20);
x_94 = lean::box(0);
x_4 = x_94;
goto lbl_5;
}
}
case 13:
{
obj* x_96; 
lean::dec(x_8);
x_96 = lean::box(0);
x_4 = x_96;
goto lbl_5;
}
default:
{
obj* x_99; 
lean::dec(x_11);
lean::dec(x_8);
x_99 = lean::box(0);
x_4 = x_99;
goto lbl_5;
}
}
}
else
{
obj* x_101; 
lean::dec(x_8);
x_101 = lean::box(0);
x_4 = x_101;
goto lbl_5;
}
lbl_5:
{
obj* x_103; obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_4);
x_103 = lean::mk_nat_obj(0ul);
x_104 = l_Array_reverseAux___main___rarg(x_3, x_103);
x_105 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_104, x_104, x_103, x_1);
lean::dec(x_104);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_2);
return x_107;
}
lbl_7:
{
obj* x_108; obj* x_109; 
x_108 = lean::array_pop(x_1);
x_109 = lean::array_push(x_3, x_6);
x_1 = x_108;
x_3 = x_109;
goto _start;
}
}
}
obj* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = lean::mk_array(x_0, x_3);
x_5 = l_Array_empty___closed__1;
x_6 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_1, x_2, x_4, x_5);
return x_6;
}
}
obj* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_9 = lean::array_fset(x_2, x_1, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
x_17 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_14);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::array_fset(x_9, x_1, x_18);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_19;
goto _start;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_24 = x_7;
} else {
 lean::inc(x_22);
 lean::dec(x_7);
 x_24 = lean::box(0);
}
x_25 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_22);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::array_fset(x_9, x_1, x_26);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_4; obj* x_5; 
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
switch (lean::obj_tag(x_5)) {
case 2:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; uint8 x_18; 
x_7 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_release(x_1, 1);
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_11 = x_1;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_1);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_5, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_5, 2);
lean::inc(x_16);
x_18 = lean::nat_dec_eq(x_0, x_12);
lean::dec(x_12);
if (x_18 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_16);
x_22 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_9);
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_5);
lean::cnstr_set(x_23, 2, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*3, x_4);
x_24 = x_23;
return x_24;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_5);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_16);
if (lean::is_scalar(x_11)) {
 x_27 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_27 = x_11;
}
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set(x_27, 2, x_9);
lean::cnstr_set_scalar(x_27, sizeof(void*)*3, x_4);
x_28 = x_27;
return x_28;
}
}
default:
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 1);
 x_33 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_1);
 x_33 = lean::box(0);
}
x_34 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_31);
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_29);
lean::cnstr_set(x_35, 1, x_5);
lean::cnstr_set(x_35, 2, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_4);
x_36 = x_35;
return x_36;
}
}
}
case 7:
{
obj* x_37; obj* x_39; uint8 x_41; obj* x_42; obj* x_44; uint8 x_45; 
x_37 = lean::cnstr_get(x_1, 0);
x_39 = lean::cnstr_get(x_1, 1);
x_41 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_42 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_44 = x_1;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::inc(x_42);
 lean::dec(x_1);
 x_44 = lean::box(0);
}
x_45 = lean::nat_dec_eq(x_0, x_37);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_42);
if (lean::is_scalar(x_44)) {
 x_47 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_47 = x_44;
}
lean::cnstr_set(x_47, 0, x_37);
lean::cnstr_set(x_47, 1, x_39);
lean::cnstr_set(x_47, 2, x_46);
lean::cnstr_set_scalar(x_47, sizeof(void*)*3, x_41);
x_48 = x_47;
return x_48;
}
else
{
lean::dec(x_44);
lean::dec(x_39);
lean::dec(x_37);
return x_42;
}
}
case 10:
{
obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_52 = lean::cnstr_get(x_1, 0);
x_54 = lean::cnstr_get(x_1, 1);
x_56 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_58 = x_1;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_1);
 x_58 = lean::box(0);
}
x_59 = lean::mk_nat_obj(0ul);
x_60 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_0, x_59, x_56);
if (lean::is_scalar(x_58)) {
 x_61 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_61 = x_58;
}
lean::cnstr_set(x_61, 0, x_52);
lean::cnstr_set(x_61, 1, x_54);
lean::cnstr_set(x_61, 2, x_60);
return x_61;
}
default:
{
obj* x_62; 
x_62 = lean::box(0);
x_2 = x_62;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_64; 
lean::dec(x_2);
x_64 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_65 = l_Lean_IR_FnBody_body___main(x_1);
x_66 = lean::box(13);
x_67 = l_Lean_IR_FnBody_setBody___main(x_1, x_66);
x_68 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_65);
x_69 = l_Lean_IR_FnBody_setBody___main(x_67, x_68);
return x_69;
}
else
{
return x_1;
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_2);
if (lean::obj_tag(x_8) == 0)
{
x_2 = x_10;
goto _start;
}
else
{
obj* x_13; uint8 x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = 1;
x_17 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_9);
lean::cnstr_set(x_17, 2, x_3);
lean::cnstr_set_scalar(x_17, sizeof(void*)*3, x_16);
x_18 = x_17;
x_2 = x_10;
x_3 = x_18;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_mkSlowPath(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_0, x_3);
x_5 = lean::mk_nat_obj(1ul);
x_6 = 1;
x_7 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set_scalar(x_7, sizeof(void*)*3, x_6);
x_8 = x_7;
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_2, x_2, x_9, x_8);
return x_10;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1ul);
x_2 = lean::nat_add(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFresh(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExpandResetReuse_mkFresh___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_ExpandResetReuse_mkFresh(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_sub(x_3, x_9);
lean::dec(x_3);
x_12 = lean::nat_sub(x_2, x_10);
x_13 = lean::nat_sub(x_12, x_9);
lean::dec(x_12);
x_15 = lean::box(0);
x_16 = lean::array_get(x_15, x_1, x_13);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_20; obj* x_24; uint8 x_25; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; 
x_17 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_6);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
lean::inc(x_0);
x_24 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_0);
x_25 = 1;
lean::inc(x_18);
x_27 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_27, 0, x_18);
lean::cnstr_set(x_27, 1, x_9);
lean::cnstr_set(x_27, 2, x_4);
lean::cnstr_set_scalar(x_27, sizeof(void*)*3, x_25);
x_28 = x_27;
x_29 = 7;
x_30 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_30, 0, x_18);
lean::cnstr_set(x_30, 1, x_24);
lean::cnstr_set(x_30, 2, x_28);
lean::cnstr_set_scalar(x_30, sizeof(void*)*3, x_29);
x_31 = x_30;
x_3 = x_10;
x_4 = x_31;
x_6 = x_20;
goto _start;
}
else
{
lean::dec(x_13);
lean::dec(x_16);
x_3 = x_10;
goto _start;
}
}
else
{
obj* x_38; 
lean::dec(x_3);
lean::dec(x_0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_4);
lean::cnstr_set(x_38, 1, x_6);
return x_38;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::array_get_size(x_1);
lean::inc(x_5);
x_7 = l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_0, x_1, x_5, x_5, x_2, x_3, x_4);
lean::dec(x_5);
return x_7;
}
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Nat_mfoldAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_3, x_7);
x_9 = lean::nat_sub(x_2, x_3);
lean::dec(x_3);
x_11 = l_Lean_IR_Arg_Inhabited;
x_12 = lean::array_get(x_11, x_1, x_9);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_12);
lean::cnstr_set(x_14, 3, x_4);
x_3 = x_8;
x_4 = x_14;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
}
}
obj* l_Lean_IR_ExpandResetReuse_setFields(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::array_get_size(x_1);
lean::inc(x_3);
x_5 = l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_0, x_1, x_3, x_3, x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_setFields___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_setFields(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::nat_dec_eq(x_3, x_0);
lean::dec(x_3);
if (x_10 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_5);
return x_15;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; usize x_4; usize x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::array_get_size(x_2);
x_4 = lean::usize_of_nat(x_1);
x_5 = lean::usize_modn(x_4, x_3);
lean::dec(x_3);
x_7 = lean::array_uget(x_2, x_5);
x_8 = l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_1, x_7);
return x_8;
}
}
uint8 l_Lean_IR_ExpandResetReuse_isSelfSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_0, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
switch (lean::obj_tag(x_7)) {
case 3:
{
obj* x_10; obj* x_12; uint8 x_15; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::nat_dec_eq(x_10, x_2);
lean::dec(x_10);
if (x_15 == 0)
{
uint8 x_18; 
lean::dec(x_12);
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = lean::nat_dec_eq(x_12, x_1);
lean::dec(x_12);
return x_19;
}
}
default:
{
uint8 x_22; 
lean::dec(x_7);
x_22 = 0;
return x_22;
}
}
}
}
else
{
uint8 x_23; 
x_23 = 0;
return x_23;
}
}
}
obj* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
uint8 l_Lean_IR_ExpandResetReuse_isSelfUSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
switch (lean::obj_tag(x_6)) {
case 4:
{
obj* x_9; obj* x_11; uint8 x_14; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::nat_dec_eq(x_9, x_2);
lean::dec(x_9);
if (x_14 == 0)
{
uint8 x_17; 
lean::dec(x_11);
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = lean::nat_dec_eq(x_11, x_1);
lean::dec(x_11);
return x_18;
}
}
default:
{
uint8 x_21; 
lean::dec(x_6);
x_21 = 0;
return x_21;
}
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
uint8 l_Lean_IR_ExpandResetReuse_isSelfSSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_0, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
switch (lean::obj_tag(x_7)) {
case 5:
{
obj* x_10; obj* x_12; obj* x_14; uint8 x_17; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 2);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::nat_dec_eq(x_2, x_10);
lean::dec(x_10);
if (x_17 == 0)
{
uint8 x_21; 
lean::dec(x_12);
lean::dec(x_14);
x_21 = 0;
return x_21;
}
else
{
uint8 x_22; 
x_22 = lean::nat_dec_eq(x_12, x_3);
lean::dec(x_12);
if (x_22 == 0)
{
uint8 x_25; 
lean::dec(x_14);
x_25 = 0;
return x_25;
}
else
{
uint8 x_26; 
x_26 = lean::nat_dec_eq(x_14, x_1);
lean::dec(x_14);
return x_26;
}
}
}
default:
{
uint8 x_29; 
lean::dec(x_7);
x_29 = 0;
return x_29;
}
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_9 = lean::array_fset(x_2, x_1, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
x_17 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_14);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::array_fset(x_9, x_1, x_18);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_19;
goto _start;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_24 = x_7;
} else {
 lean::inc(x_22);
 lean::dec(x_7);
 x_24 = lean::box(0);
}
x_25 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_22);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::array_fset(x_9, x_1, x_26);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; uint8 x_13; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_12 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_1);
 x_12 = lean::box(0);
}
x_13 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_0, x_4, x_6, x_8);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_10);
if (lean::is_scalar(x_12)) {
 x_15 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_15 = x_12;
}
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_6);
lean::cnstr_set(x_15, 2, x_8);
lean::cnstr_set(x_15, 3, x_14);
return x_15;
}
else
{
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_8);
x_1 = x_10;
goto _start;
}
}
case 4:
{
obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; uint8 x_30; 
x_21 = lean::cnstr_get(x_1, 0);
x_23 = lean::cnstr_get(x_1, 1);
x_25 = lean::cnstr_get(x_1, 2);
x_27 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_29 = x_1;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_1);
 x_29 = lean::box(0);
}
x_30 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_0, x_21, x_23, x_25);
if (x_30 == 0)
{
obj* x_31; obj* x_32; 
x_31 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_27);
if (lean::is_scalar(x_29)) {
 x_32 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_32 = x_29;
}
lean::cnstr_set(x_32, 0, x_21);
lean::cnstr_set(x_32, 1, x_23);
lean::cnstr_set(x_32, 2, x_25);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
else
{
lean::dec(x_25);
lean::dec(x_29);
lean::dec(x_23);
lean::dec(x_21);
x_1 = x_27;
goto _start;
}
}
case 5:
{
obj* x_38; obj* x_40; obj* x_42; obj* x_44; uint8 x_46; obj* x_47; obj* x_49; uint8 x_50; 
x_38 = lean::cnstr_get(x_1, 0);
x_40 = lean::cnstr_get(x_1, 1);
x_42 = lean::cnstr_get(x_1, 2);
x_44 = lean::cnstr_get(x_1, 3);
x_46 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_47 = lean::cnstr_get(x_1, 4);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 lean::cnstr_set(x_1, 4, lean::box(0));
 x_49 = x_1;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_47);
 lean::dec(x_1);
 x_49 = lean::box(0);
}
x_50 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_0, x_38, x_40, x_42, x_44);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_47);
if (lean::is_scalar(x_49)) {
 x_52 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_52 = x_49;
}
lean::cnstr_set(x_52, 0, x_38);
lean::cnstr_set(x_52, 1, x_40);
lean::cnstr_set(x_52, 2, x_42);
lean::cnstr_set(x_52, 3, x_44);
lean::cnstr_set(x_52, 4, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*5, x_46);
x_53 = x_52;
return x_53;
}
else
{
lean::dec(x_49);
lean::dec(x_38);
lean::dec(x_40);
lean::dec(x_42);
lean::dec(x_44);
x_1 = x_47;
goto _start;
}
}
case 10:
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_60 = lean::cnstr_get(x_1, 0);
x_62 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_66 = x_1;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_1);
 x_66 = lean::box(0);
}
x_67 = lean::mk_nat_obj(0ul);
x_68 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_0, x_67, x_64);
if (lean::is_scalar(x_66)) {
 x_69 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_69 = x_66;
}
lean::cnstr_set(x_69, 0, x_60);
lean::cnstr_set(x_69, 1, x_62);
lean::cnstr_set(x_69, 2, x_68);
return x_69;
}
default:
{
obj* x_70; 
x_70 = lean::box(0);
x_2 = x_70;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_72; 
lean::dec(x_2);
x_72 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = l_Lean_IR_FnBody_body___main(x_1);
x_74 = lean::box(13);
x_75 = l_Lean_IR_FnBody_setBody___main(x_1, x_74);
x_76 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_73);
x_77 = l_Lean_IR_FnBody_setBody___main(x_75, x_76);
return x_77;
}
else
{
return x_1;
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_fget(x_4, x_3);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_12 = lean::array_fset(x_4, x_3, x_11);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
lean::inc(x_2);
x_21 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_17);
if (lean::is_scalar(x_19)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_19;
}
lean::cnstr_set(x_22, 0, x_15);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::array_fset(x_12, x_3, x_22);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_23;
goto _start;
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_28 = x_10;
} else {
 lean::inc(x_26);
 lean::dec(x_10);
 x_28 = lean::box(0);
}
lean::inc(x_2);
x_30 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_26);
if (lean::is_scalar(x_28)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_28;
}
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::array_fset(x_12, x_3, x_31);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_32;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_3)) {
case 0:
{
uint8 x_6; obj* x_7; 
x_6 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
switch (lean::obj_tag(x_7)) {
case 2:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; uint8 x_18; obj* x_19; uint8 x_21; 
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_release(x_3, 1);
 lean::cnstr_set(x_3, 2, lean::box(0));
 x_13 = x_3;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_3);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*3);
x_19 = lean::cnstr_get(x_7, 2);
lean::inc(x_19);
x_21 = lean::nat_dec_eq(x_1, x_14);
lean::dec(x_14);
if (x_21 == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_19);
lean::dec(x_16);
x_25 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_11);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_7);
lean::cnstr_set(x_26, 2, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*3, x_6);
x_27 = x_26;
return x_27;
}
else
{
obj* x_31; obj* x_34; 
lean::dec(x_7);
lean::dec(x_13);
lean::inc(x_2);
x_31 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_9, x_2, x_11);
lean::dec(x_9);
lean::inc(x_2);
x_34 = l_Lean_IR_ExpandResetReuse_setFields(x_2, x_19, x_31);
lean::dec(x_19);
if (x_18 == 0)
{
obj* x_38; 
lean::dec(x_2);
lean::dec(x_16);
x_38 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_34);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_16, 1);
lean::inc(x_39);
lean::dec(x_16);
x_42 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_42, 0, x_2);
lean::cnstr_set(x_42, 1, x_39);
lean::cnstr_set(x_42, 2, x_34);
x_43 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_0, x_42);
return x_43;
}
}
}
default:
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_44 = lean::cnstr_get(x_3, 0);
x_46 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 1);
 x_48 = x_3;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_3);
 x_48 = lean::box(0);
}
x_49 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_46);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_44);
lean::cnstr_set(x_50, 1, x_7);
lean::cnstr_set(x_50, 2, x_49);
lean::cnstr_set_scalar(x_50, sizeof(void*)*3, x_6);
x_51 = x_50;
return x_51;
}
}
}
case 7:
{
obj* x_52; obj* x_54; uint8 x_56; obj* x_57; obj* x_59; uint8 x_60; 
x_52 = lean::cnstr_get(x_3, 0);
x_54 = lean::cnstr_get(x_3, 1);
x_56 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_57 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 x_59 = x_3;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::inc(x_57);
 lean::dec(x_3);
 x_59 = lean::box(0);
}
x_60 = lean::nat_dec_eq(x_1, x_52);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_57);
if (lean::is_scalar(x_59)) {
 x_62 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_62 = x_59;
}
lean::cnstr_set(x_62, 0, x_52);
lean::cnstr_set(x_62, 1, x_54);
lean::cnstr_set(x_62, 2, x_61);
lean::cnstr_set_scalar(x_62, sizeof(void*)*3, x_56);
x_63 = x_62;
return x_63;
}
else
{
obj* x_67; 
lean::dec(x_52);
lean::dec(x_59);
lean::dec(x_54);
x_67 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_67, 0, x_2);
lean::cnstr_set(x_67, 1, x_57);
return x_67;
}
}
case 10:
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_68 = lean::cnstr_get(x_3, 0);
x_70 = lean::cnstr_get(x_3, 1);
x_72 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 x_74 = x_3;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_3);
 x_74 = lean::box(0);
}
x_75 = lean::mk_nat_obj(0ul);
x_76 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_0, x_1, x_2, x_75, x_72);
if (lean::is_scalar(x_74)) {
 x_77 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_77 = x_74;
}
lean::cnstr_set(x_77, 0, x_68);
lean::cnstr_set(x_77, 1, x_70);
lean::cnstr_set(x_77, 2, x_76);
return x_77;
}
default:
{
obj* x_78; 
x_78 = lean::box(0);
x_4 = x_78;
goto lbl_5;
}
}
lbl_5:
{
uint8 x_80; 
lean::dec(x_4);
x_80 = l_Lean_IR_FnBody_isTerminal___main(x_3);
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_81 = l_Lean_IR_FnBody_body___main(x_3);
x_82 = lean::box(13);
x_83 = l_Lean_IR_FnBody_setBody___main(x_3, x_82);
x_84 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_81);
x_85 = l_Lean_IR_FnBody_setBody___main(x_83, x_84);
return x_85;
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFastPath(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_1);
x_7 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_4, x_0, x_1, x_3);
x_8 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
obj* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_ExpandResetReuse_expand(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_8 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_3, x_4, x_1);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
lean::inc(x_5);
lean::inc(x_4);
x_16 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_2, x_4, x_11, x_5);
lean::inc(x_4);
x_18 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_2, x_4, x_11, x_5, x_6, x_7);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_18, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_18, 1);
lean::inc(x_22);
lean::dec(x_18);
x_25 = l_Array_empty___closed__1;
x_26 = lean::apply_4(x_0, x_20, x_25, x_6, x_22);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_29);
x_33 = lean::cnstr_get(x_32, 0);
x_35 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_32);
 x_37 = lean::box(0);
}
x_38 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_38, 0, x_4);
lean::inc(x_33);
x_40 = l_Lean_IR_mkIf(x_33, x_16, x_27);
x_41 = 1;
x_42 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_42, 0, x_33);
lean::cnstr_set(x_42, 1, x_38);
lean::cnstr_set(x_42, 2, x_40);
lean::cnstr_set_scalar(x_42, sizeof(void*)*3, x_41);
x_43 = x_42;
x_44 = l_Lean_IR_reshape(x_9, x_43);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_35);
return x_45;
}
}
obj* l_Lean_IR_ExpandResetReuse_expand___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_IR_ExpandResetReuse_expand(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
return x_8;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::array_fget(x_1, x_0);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_12 = lean::array_fset(x_1, x_0, x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = l_Array_empty___closed__1;
lean::inc(x_2);
x_20 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_15, x_18, x_2, x_3);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_13);
lean::cnstr_set(x_26, 1, x_21);
x_27 = lean::mk_nat_obj(1ul);
x_28 = lean::nat_add(x_0, x_27);
x_29 = lean::array_fset(x_12, x_0, x_26);
lean::dec(x_0);
x_0 = x_28;
x_1 = x_29;
x_3 = x_23;
goto _start;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_32 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_34 = x_10;
} else {
 lean::inc(x_32);
 lean::dec(x_10);
 x_34 = lean::box(0);
}
x_35 = l_Array_empty___closed__1;
lean::inc(x_2);
x_37 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_32, x_35, x_2, x_3);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::is_scalar(x_34)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_34;
}
lean::cnstr_set(x_43, 0, x_38);
x_44 = lean::mk_nat_obj(1ul);
x_45 = lean::nat_add(x_0, x_44);
x_46 = lean::array_fset(x_12, x_0, x_43);
lean::dec(x_0);
x_0 = x_45;
x_1 = x_46;
x_3 = x_40;
goto _start;
}
}
}
}
obj* _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExpandResetReuse_searchAndExpand___main), 4, 0);
return x_0;
}
}
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
switch (lean::obj_tag(x_6)) {
case 1:
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; uint8 x_18; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_6, 1);
lean::inc(x_14);
lean::dec(x_6);
lean::inc(x_10);
x_18 = l_Lean_IR_ExpandResetReuse_consumed___main(x_8, x_10);
if (x_18 == 0)
{
obj* x_22; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_14);
x_22 = l_Lean_IR_push(x_1, x_0);
x_0 = x_10;
x_1 = x_22;
goto _start;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_0);
x_25 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1;
x_26 = l_Lean_IR_ExpandResetReuse_expand(x_25, x_1, x_8, x_12, x_14, x_10, x_2, x_3);
lean::dec(x_8);
return x_26;
}
}
default:
{
obj* x_29; 
lean::dec(x_6);
x_29 = lean::box(0);
x_4 = x_29;
goto lbl_5;
}
}
}
case 1:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_Array_empty___closed__1;
lean::inc(x_2);
x_41 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_34, x_39, x_2, x_3);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = lean::box(13);
if (lean::is_scalar(x_38)) {
 x_48 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_48 = x_38;
}
lean::cnstr_set(x_48, 0, x_30);
lean::cnstr_set(x_48, 1, x_32);
lean::cnstr_set(x_48, 2, x_42);
lean::cnstr_set(x_48, 3, x_47);
x_49 = l_Lean_IR_push(x_1, x_48);
x_0 = x_36;
x_1 = x_49;
x_3 = x_44;
goto _start;
}
case 10:
{
obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_51 = lean::cnstr_get(x_0, 0);
x_53 = lean::cnstr_get(x_0, 1);
x_55 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_57 = x_0;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_0);
 x_57 = lean::box(0);
}
x_58 = lean::mk_nat_obj(0ul);
x_59 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(x_58, x_55, x_2, x_3);
x_60 = lean::cnstr_get(x_59, 0);
x_62 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 x_64 = x_59;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_59);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_65 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_65 = x_57;
}
lean::cnstr_set(x_65, 0, x_51);
lean::cnstr_set(x_65, 1, x_53);
lean::cnstr_set(x_65, 2, x_60);
x_66 = l_Lean_IR_reshape(x_1, x_65);
if (lean::is_scalar(x_64)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_64;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_62);
return x_67;
}
default:
{
obj* x_68; 
x_68 = lean::box(0);
x_4 = x_68;
goto lbl_5;
}
}
lbl_5:
{
uint8 x_70; 
lean::dec(x_4);
x_70 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_70 == 0)
{
obj* x_71; obj* x_72; 
x_71 = l_Lean_IR_FnBody_body___main(x_0);
x_72 = l_Lean_IR_push(x_1, x_0);
x_0 = x_71;
x_1 = x_72;
goto _start;
}
else
{
obj* x_75; obj* x_76; 
lean::dec(x_2);
x_75 = l_Lean_IR_reshape(x_1, x_0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_3);
return x_76;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_normalizeIds(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; uint8 x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::inc(x_1);
x_10 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_1);
x_11 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_13 = l_Lean_IR_MaxIndex_collectDecl___main(x_1, x_11);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_13, x_15);
lean::dec(x_13);
x_18 = l_Array_empty___closed__1;
x_19 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_7, x_18, x_10, x_16);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
lean::dec(x_19);
if (lean::is_scalar(x_14)) {
 x_23 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_23 = x_14;
}
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_4);
lean::cnstr_set(x_23, 2, x_20);
lean::cnstr_set_scalar(x_23, sizeof(void*)*3, x_6);
x_24 = x_23;
return x_24;
}
else
{
return x_1;
}
}
}
obj* l_Lean_IR_Decl_expandResetReuse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_ExpandResetReuse_main(x_0);
return x_1;
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
