// Lean compiler output
// Module: init.lean.metavarcontext
// Imports: init.lean.localcontext
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
extern "C" {
uint8 lean_metavar_ctx_is_level_assigned(obj*, obj*);
uint8 lean_name_dec_eq(obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(obj*, usize, obj*);
usize l_USize_mul(usize, usize);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1___boxed(obj*, obj*);
uint8 l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(obj*, obj*);
obj* lean_nat_sub(obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2___boxed(obj*, obj*, obj*);
usize l_USize_shift__right(usize, usize);
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* lean_metavar_ctx_erase_delayed(obj*, obj*);
obj* l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3___boxed(obj*, obj*, obj*);
obj* lean_metavar_ctx_get_delayed_assignment(obj*, obj*);
usize l_USize_sub(usize, usize);
obj* l_Lean_MetavarContext_mkMetavarContext___closed__1;
uint8 l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* lean_metavar_ctx_get_expr_assignment(obj*, obj*);
obj* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(obj*, usize, obj*);
uint8 l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___rarg(obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mkCollisionNode___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(obj*, obj*, obj*, obj*, obj*);
usize lean_name_hash_usize(obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2___boxed(obj*, obj*, obj*);
usize l_USize_add(usize, usize);
obj* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(obj*, obj*, obj*, obj*);
uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* lean_mk_metavar_ctx(obj*);
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(obj*, usize, obj*);
extern obj* l_PersistentHashMap_empty___closed__3;
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* lean_nat_add(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* lean_metavar_ctx_assign_expr(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_mkDecl___spec__3(obj*, obj*, obj*, obj*);
extern usize l_PersistentHashMap_insertAux___main___rarg___closed__2;
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(obj*, obj*, obj*);
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(obj*, usize, obj*);
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2___boxed(obj*, obj*, obj*);
obj* lean_metavar_ctx_get_level_assignment(obj*, obj*);
uint8 lean_metavar_ctx_is_delayed_assigned(obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(obj*, usize, usize, obj*, obj*);
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_mkDecl___spec__1(obj*, obj*, obj*);
uint8 l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(obj*, usize, obj*);
obj* l_Lean_MetavarContext_isDelayedAssigned___boxed(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_MetavarContext_isLevelAssigned___boxed(obj*, obj*);
extern obj* l_PersistentHashMap_insertAux___main___rarg___closed__3;
obj* l_Array_size(obj*, obj*);
obj* l_Array_eraseIdx_x27___rarg(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_isUnaryNode___rarg(obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
uint8 lean_metavar_ctx_is_expr_assigned(obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_indexOfAux___main___at_Lean_LocalContext_erase___spec__3(obj*, obj*, obj*);
obj* lean_metavar_ctx_mk_decl(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(obj*, usize, usize, obj*, obj*);
obj* lean_metavar_ctx_find_decl(obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(obj*, obj*, obj*);
obj* l_Lean_MetavarContext_isExprAssigned___boxed(obj*, obj*);
obj* lean_metavar_ctx_assign_delayed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(obj*, usize, usize, obj*, obj*);
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(obj*, obj*, obj*);
obj* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1___boxed(obj*, obj*);
uint8 l_USize_decLe(usize, usize);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2___boxed(obj*, obj*, obj*);
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(obj*, usize, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(obj*, usize, obj*);
usize l_USize_land(usize, usize);
obj* lean_usize_to_nat(usize);
obj* lean_metavar_ctx_assign_level(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(obj*, usize, obj*);
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(obj*, usize, usize, obj*, obj*);
obj* l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1___boxed(obj*, obj*);
obj* _init_l_Lean_MetavarContext_mkMetavarContext___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_PersistentHashMap_empty___closed__3;
x_2 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
lean::cnstr_set(x_2, 3, x_1);
return x_2;
}
}
obj* lean_mk_metavar_ctx(obj* x_1) {
_start:
{
obj* x_2; 
lean::dec(x_1);
x_2 = l_Lean_MetavarContext_mkMetavarContext___closed__1;
return x_2;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_mkDecl___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean_nat_add(x_2, x_19);
lean::dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_1);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_1, 1);
lean::dec(x_23);
x_24 = lean::cnstr_get(x_1, 0);
lean::dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4(usize x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; obj* x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; usize x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_name_hash_usize(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_add(x_5, x_18);
lean::dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(obj* x_1, usize x_2, usize x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; usize x_8; usize x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean::obj_tag(x_15)) {
case 0:
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
x_21 = lean_name_dec_eq(x_4, x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::free_heap_obj(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_24);
return x_1;
}
else
{
obj* x_25; 
lean::dec(x_20);
lean::dec(x_19);
lean::cnstr_set(x_15, 1, x_5);
lean::cnstr_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
}
else
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::cnstr_get(x_15, 0);
x_27 = lean::cnstr_get(x_15, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_15);
x_28 = lean_name_dec_eq(x_4, x_26);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_31);
return x_1;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_27);
lean::dec(x_26);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_15);
if (x_34 == 0)
{
obj* x_35; usize x_36; usize x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_35, x_36, x_37, x_4, x_5);
lean::cnstr_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_39);
return x_1;
}
else
{
obj* x_40; usize x_41; usize x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_15, 0);
lean::inc(x_40);
lean::dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
obj* x_46; obj* x_47; 
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_4);
lean::cnstr_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
obj* x_48; usize x_49; usize x_50; usize x_51; usize x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_56; 
lean::dec(x_53);
lean::dec(x_5);
lean::dec(x_4);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_48);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_60; obj* x_61; obj* x_62; uint8 x_63; 
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
} else {
 lean::dec_ref(x_57);
 x_62 = lean::box(0);
}
x_63 = lean_name_dec_eq(x_4, x_60);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean::dec(x_53);
x_67 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_61);
lean::dec(x_60);
if (lean::is_scalar(x_62)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_62;
}
lean::cnstr_set(x_68, 0, x_4);
lean::cnstr_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean::dec(x_53);
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
obj* x_71; obj* x_72; usize x_73; usize x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = lean::cnstr_get(x_57, 0);
lean::inc(x_71);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_72 = x_57;
} else {
 lean::dec_ref(x_57);
 x_72 = lean::box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean::is_scalar(x_72)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_72;
}
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean::dec(x_53);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
default: 
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_4);
lean::cnstr_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean::dec(x_53);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
obj* x_82; obj* x_83; usize x_84; uint8 x_85; 
x_82 = lean::mk_nat_obj(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_mkDecl___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
obj* x_86; obj* x_87; uint8 x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean::dec(x_86);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_83, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_83, 1);
lean::inc(x_90);
lean::dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean::dec(x_90);
lean::dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_mkDecl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean_name_hash_usize(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_6, x_10);
lean::dec(x_6);
lean::cnstr_set(x_1, 1, x_11);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
else
{
obj* x_12; obj* x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean_name_hash_usize(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean_nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
obj* lean_metavar_ctx_mk_decl(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set(x_8, 2, x_5);
x_9 = l_PersistentHashMap_insert___at_Lean_MetavarContext_mkDecl___spec__1(x_7, x_2, x_8);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_5);
x_15 = l_PersistentHashMap_insert___at_Lean_MetavarContext_mkDecl___spec__1(x_10, x_2, x_14);
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_13);
return x_16;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
usize x_7; obj* x_8; 
x_7 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_8 = l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_7 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean::dec(x_4);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_12);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; 
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
obj* x_16; usize x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_16, x_17, x_3);
lean::dec(x_16);
return x_18;
}
default: 
{
obj* x_19; 
x_19 = lean::box(0);
return x_19;
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(x_20, x_21, lean::box(0), x_22, x_3);
return x_23;
}
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_3, x_4, x_2);
return x_5;
}
}
obj* lean_metavar_ctx_find_decl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean_nat_add(x_2, x_19);
lean::dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_1);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_1, 1);
lean::dec(x_23);
x_24 = lean::cnstr_get(x_1, 0);
lean::dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4(usize x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; obj* x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; usize x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_name_hash_usize(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_add(x_5, x_18);
lean::dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(obj* x_1, usize x_2, usize x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; usize x_8; usize x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean::obj_tag(x_15)) {
case 0:
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
x_21 = lean_name_dec_eq(x_4, x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::free_heap_obj(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_24);
return x_1;
}
else
{
obj* x_25; 
lean::dec(x_20);
lean::dec(x_19);
lean::cnstr_set(x_15, 1, x_5);
lean::cnstr_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
}
else
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::cnstr_get(x_15, 0);
x_27 = lean::cnstr_get(x_15, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_15);
x_28 = lean_name_dec_eq(x_4, x_26);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_31);
return x_1;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_27);
lean::dec(x_26);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_15);
if (x_34 == 0)
{
obj* x_35; usize x_36; usize x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_35, x_36, x_37, x_4, x_5);
lean::cnstr_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_39);
return x_1;
}
else
{
obj* x_40; usize x_41; usize x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_15, 0);
lean::inc(x_40);
lean::dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
obj* x_46; obj* x_47; 
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_4);
lean::cnstr_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
obj* x_48; usize x_49; usize x_50; usize x_51; usize x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_56; 
lean::dec(x_53);
lean::dec(x_5);
lean::dec(x_4);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_48);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_60; obj* x_61; obj* x_62; uint8 x_63; 
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
} else {
 lean::dec_ref(x_57);
 x_62 = lean::box(0);
}
x_63 = lean_name_dec_eq(x_4, x_60);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean::dec(x_53);
x_67 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_61);
lean::dec(x_60);
if (lean::is_scalar(x_62)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_62;
}
lean::cnstr_set(x_68, 0, x_4);
lean::cnstr_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean::dec(x_53);
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
obj* x_71; obj* x_72; usize x_73; usize x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = lean::cnstr_get(x_57, 0);
lean::inc(x_71);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_72 = x_57;
} else {
 lean::dec_ref(x_57);
 x_72 = lean::box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean::is_scalar(x_72)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_72;
}
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean::dec(x_53);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
default: 
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_4);
lean::cnstr_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean::dec(x_53);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
obj* x_82; obj* x_83; usize x_84; uint8 x_85; 
x_82 = lean::mk_nat_obj(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
obj* x_86; obj* x_87; uint8 x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean::dec(x_86);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_83, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_83, 1);
lean::inc(x_90);
lean::dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean::dec(x_90);
lean::dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean_name_hash_usize(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_6, x_10);
lean::dec(x_6);
lean::cnstr_set(x_1, 1, x_11);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
else
{
obj* x_12; obj* x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean_name_hash_usize(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean_nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
obj* lean_metavar_ctx_assign_level(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(x_5, x_2, x_3);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_11 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(x_8, x_2, x_3);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_9);
lean::cnstr_set(x_12, 3, x_10);
return x_12;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
usize x_7; obj* x_8; 
x_7 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_8 = l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_7 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean_nat_add(x_2, x_19);
lean::dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_1);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_1, 1);
lean::dec(x_23);
x_24 = lean::cnstr_get(x_1, 0);
lean::dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4(usize x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; obj* x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; usize x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_name_hash_usize(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_add(x_5, x_18);
lean::dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(obj* x_1, usize x_2, usize x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; usize x_8; usize x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean::obj_tag(x_15)) {
case 0:
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
x_21 = lean_name_dec_eq(x_4, x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::free_heap_obj(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_24);
return x_1;
}
else
{
obj* x_25; 
lean::dec(x_20);
lean::dec(x_19);
lean::cnstr_set(x_15, 1, x_5);
lean::cnstr_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
}
else
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::cnstr_get(x_15, 0);
x_27 = lean::cnstr_get(x_15, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_15);
x_28 = lean_name_dec_eq(x_4, x_26);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_31);
return x_1;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_27);
lean::dec(x_26);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_15);
if (x_34 == 0)
{
obj* x_35; usize x_36; usize x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_35, x_36, x_37, x_4, x_5);
lean::cnstr_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_39);
return x_1;
}
else
{
obj* x_40; usize x_41; usize x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_15, 0);
lean::inc(x_40);
lean::dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
obj* x_46; obj* x_47; 
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_4);
lean::cnstr_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
obj* x_48; usize x_49; usize x_50; usize x_51; usize x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_56; 
lean::dec(x_53);
lean::dec(x_5);
lean::dec(x_4);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_48);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_60; obj* x_61; obj* x_62; uint8 x_63; 
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
} else {
 lean::dec_ref(x_57);
 x_62 = lean::box(0);
}
x_63 = lean_name_dec_eq(x_4, x_60);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean::dec(x_53);
x_67 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_61);
lean::dec(x_60);
if (lean::is_scalar(x_62)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_62;
}
lean::cnstr_set(x_68, 0, x_4);
lean::cnstr_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean::dec(x_53);
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
obj* x_71; obj* x_72; usize x_73; usize x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = lean::cnstr_get(x_57, 0);
lean::inc(x_71);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_72 = x_57;
} else {
 lean::dec_ref(x_57);
 x_72 = lean::box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean::is_scalar(x_72)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_72;
}
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean::dec(x_53);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
default: 
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_4);
lean::cnstr_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean::dec(x_53);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
obj* x_82; obj* x_83; usize x_84; uint8 x_85; 
x_82 = lean::mk_nat_obj(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
obj* x_86; obj* x_87; uint8 x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean::dec(x_86);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_83, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_83, 1);
lean::inc(x_90);
lean::dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean::dec(x_90);
lean::dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean_name_hash_usize(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_6, x_10);
lean::dec(x_6);
lean::cnstr_set(x_1, 1, x_11);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
else
{
obj* x_12; obj* x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean_name_hash_usize(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean_nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
obj* lean_metavar_ctx_assign_expr(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 2);
x_6 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(x_5, x_2, x_3);
lean::cnstr_set(x_1, 2, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_11 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(x_9, x_2, x_3);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 2, x_11);
lean::cnstr_set(x_12, 3, x_10);
return x_12;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
usize x_7; obj* x_8; 
x_7 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_8 = l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_7 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean_nat_add(x_2, x_19);
lean::dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_1);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_1, 1);
lean::dec(x_23);
x_24 = lean::cnstr_get(x_1, 0);
lean::dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean::dec(x_2);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(usize x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; obj* x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; usize x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_name_hash_usize(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_add(x_5, x_18);
lean::dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(obj* x_1, usize x_2, usize x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; usize x_8; usize x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean::obj_tag(x_15)) {
case 0:
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
x_21 = lean_name_dec_eq(x_4, x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::free_heap_obj(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_24);
return x_1;
}
else
{
obj* x_25; 
lean::dec(x_20);
lean::dec(x_19);
lean::cnstr_set(x_15, 1, x_5);
lean::cnstr_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
}
else
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::cnstr_get(x_15, 0);
x_27 = lean::cnstr_get(x_15, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_15);
x_28 = lean_name_dec_eq(x_4, x_26);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_31);
return x_1;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_27);
lean::dec(x_26);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_15);
if (x_34 == 0)
{
obj* x_35; usize x_36; usize x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_35, x_36, x_37, x_4, x_5);
lean::cnstr_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_39);
return x_1;
}
else
{
obj* x_40; usize x_41; usize x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_15, 0);
lean::inc(x_40);
lean::dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
obj* x_46; obj* x_47; 
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_4);
lean::cnstr_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean::dec(x_12);
lean::cnstr_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
obj* x_48; usize x_49; usize x_50; usize x_51; usize x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_56; 
lean::dec(x_53);
lean::dec(x_5);
lean::dec(x_4);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_48);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_60; obj* x_61; obj* x_62; uint8 x_63; 
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
} else {
 lean::dec_ref(x_57);
 x_62 = lean::box(0);
}
x_63 = lean_name_dec_eq(x_4, x_60);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean::dec(x_53);
x_67 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_61);
lean::dec(x_60);
if (lean::is_scalar(x_62)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_62;
}
lean::cnstr_set(x_68, 0, x_4);
lean::cnstr_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean::dec(x_53);
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
obj* x_71; obj* x_72; usize x_73; usize x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = lean::cnstr_get(x_57, 0);
lean::inc(x_71);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_72 = x_57;
} else {
 lean::dec_ref(x_57);
 x_72 = lean::box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean::is_scalar(x_72)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_72;
}
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean::dec(x_53);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
default: 
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_4);
lean::cnstr_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean::dec(x_53);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
obj* x_82; obj* x_83; usize x_84; uint8 x_85; 
x_82 = lean::mk_nat_obj(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
obj* x_86; obj* x_87; uint8 x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean::dec(x_86);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_83, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_83, 1);
lean::inc(x_90);
lean::dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean::dec(x_90);
lean::dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
obj* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean_name_hash_usize(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_6, x_10);
lean::dec(x_6);
lean::cnstr_set(x_1, 1, x_11);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
else
{
obj* x_12; obj* x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean_name_hash_usize(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean_nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
obj* lean_metavar_ctx_assign_delayed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 3);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set(x_8, 2, x_5);
x_9 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(x_7, x_2, x_8);
lean::cnstr_set(x_1, 3, x_9);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_5);
x_15 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(x_13, x_2, x_14);
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_15);
return x_16;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
usize x_7; obj* x_8; 
x_7 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_8 = l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_7 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean::dec(x_4);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_12);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; 
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
obj* x_16; usize x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_16, x_17, x_3);
lean::dec(x_16);
return x_18;
}
default: 
{
obj* x_19; 
x_19 = lean::box(0);
return x_19;
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(x_20, x_21, lean::box(0), x_22, x_3);
return x_23;
}
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
obj* lean_metavar_ctx_get_level_assignment(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean::dec(x_4);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_12);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; 
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
obj* x_16; usize x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_16, x_17, x_3);
lean::dec(x_16);
return x_18;
}
default: 
{
obj* x_19; 
x_19 = lean::box(0);
return x_19;
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(x_20, x_21, lean::box(0), x_22, x_3);
return x_23;
}
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
obj* lean_metavar_ctx_get_expr_assignment(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean::dec(x_4);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_12);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; 
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
obj* x_16; usize x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_16, x_17, x_3);
lean::dec(x_16);
return x_18;
}
default: 
{
obj* x_19; 
x_19 = lean::box(0);
return x_19;
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(x_20, x_21, lean::box(0), x_22, x_3);
return x_23;
}
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
obj* lean_metavar_ctx_get_delayed_assignment(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 3);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_name_dec_eq(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_2, x_9);
lean::dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8 x_12; 
lean::dec(x_2);
x_12 = 1;
return x_12;
}
}
}
}
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
return x_12;
}
case 1:
{
obj* x_13; usize x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_13, x_14, x_3);
lean::dec(x_13);
return x_15;
}
default: 
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_17, x_18, x_3);
return x_19;
}
}
}
uint8 l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8 lean_metavar_ctx_is_level_assigned(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_MetavarContext_isLevelAssigned___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_metavar_ctx_is_level_assigned(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
return x_12;
}
case 1:
{
obj* x_13; usize x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_13, x_14, x_3);
lean::dec(x_13);
return x_15;
}
default: 
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_17, x_18, x_3);
return x_19;
}
}
}
uint8 l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8 lean_metavar_ctx_is_expr_assigned(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_MetavarContext_isExprAssigned___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_metavar_ctx_is_expr_assigned(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean::dec(x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
return x_12;
}
case 1:
{
obj* x_13; usize x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(x_13, x_14, x_3);
lean::dec(x_13);
return x_15;
}
default: 
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_17, x_18, x_3);
return x_19;
}
}
}
uint8 l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8 lean_metavar_ctx_is_delayed_assigned(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 3);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_MetavarContext_isDelayedAssigned___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_metavar_ctx_is_delayed_assigned(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean_name_dec_eq(x_3, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_13; obj* x_14; obj* x_15; 
lean::dec(x_8);
lean::dec(x_4);
x_13 = 0;
x_14 = lean::box(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_1);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_1, 0);
lean::dec(x_17);
x_18 = lean_array_set(x_4, x_8, x_9);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_18);
x_19 = 1;
x_20 = lean::box(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
x_22 = lean_array_set(x_4, x_8, x_9);
lean::dec(x_8);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = 1;
x_25 = lean::box(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
case 1:
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_10);
if (x_27 == 0)
{
obj* x_28; obj* x_29; usize x_30; obj* x_31; obj* x_32; uint8 x_33; 
x_28 = lean::cnstr_get(x_10, 0);
x_29 = lean_array_set(x_4, x_8, x_9);
x_30 = x_2 >> x_5;
x_31 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_28, x_30, x_3);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_33 = lean::unbox(x_32);
lean::dec(x_32);
if (x_33 == 0)
{
uint8 x_34; 
lean::dec(x_29);
lean::free_heap_obj(x_10);
lean::dec(x_8);
x_34 = !lean::is_exclusive(x_31);
if (x_34 == 0)
{
obj* x_35; obj* x_36; uint8 x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_31, 1);
lean::dec(x_35);
x_36 = lean::cnstr_get(x_31, 0);
lean::dec(x_36);
x_37 = 0;
x_38 = lean::box(x_37);
lean::cnstr_set(x_31, 1, x_38);
lean::cnstr_set(x_31, 0, x_1);
return x_31;
}
else
{
uint8 x_39; obj* x_40; obj* x_41; 
lean::dec(x_31);
x_39 = 0;
x_40 = lean::box(x_39);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8 x_42; 
x_42 = !lean::is_exclusive(x_1);
if (x_42 == 0)
{
obj* x_43; uint8 x_44; 
x_43 = lean::cnstr_get(x_1, 0);
lean::dec(x_43);
x_44 = !lean::is_exclusive(x_31);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_31, 0);
x_46 = lean::cnstr_get(x_31, 1);
lean::dec(x_46);
x_47 = l_PersistentHashMap_isUnaryNode___rarg(x_45);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; uint8 x_49; obj* x_50; 
lean::cnstr_set(x_10, 0, x_45);
x_48 = lean_array_set(x_29, x_8, x_10);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_48);
x_49 = 1;
x_50 = lean::box(x_49);
lean::cnstr_set(x_31, 1, x_50);
lean::cnstr_set(x_31, 0, x_1);
return x_31;
}
else
{
obj* x_51; uint8 x_52; 
lean::free_heap_obj(x_31);
lean::dec(x_45);
lean::free_heap_obj(x_10);
x_51 = lean::cnstr_get(x_47, 0);
lean::inc(x_51);
lean::dec(x_47);
x_52 = !lean::is_exclusive(x_51);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_51, 0);
x_54 = lean::cnstr_get(x_51, 1);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean_array_set(x_29, x_8, x_55);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_56);
x_57 = 1;
x_58 = lean::box(x_57);
lean::cnstr_set(x_51, 1, x_58);
lean::cnstr_set(x_51, 0, x_1);
return x_51;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; 
x_59 = lean::cnstr_get(x_51, 0);
x_60 = lean::cnstr_get(x_51, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_51);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean_array_set(x_29, x_8, x_61);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_62);
x_63 = 1;
x_64 = lean::box(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_1);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
obj* x_66; obj* x_67; 
x_66 = lean::cnstr_get(x_31, 0);
lean::inc(x_66);
lean::dec(x_31);
x_67 = l_PersistentHashMap_isUnaryNode___rarg(x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; uint8 x_69; obj* x_70; obj* x_71; 
lean::cnstr_set(x_10, 0, x_66);
x_68 = lean_array_set(x_29, x_8, x_10);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_68);
x_69 = 1;
x_70 = lean::box(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_1);
lean::cnstr_set(x_71, 1, x_70);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; uint8 x_78; obj* x_79; obj* x_80; 
lean::dec(x_66);
lean::free_heap_obj(x_10);
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
lean::dec(x_67);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_75 = x_72;
} else {
 lean::dec_ref(x_72);
 x_75 = lean::box(0);
}
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean_array_set(x_29, x_8, x_76);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_77);
x_78 = 1;
x_79 = lean::box(x_78);
if (lean::is_scalar(x_75)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_75;
}
lean::cnstr_set(x_80, 0, x_1);
lean::cnstr_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_1);
x_81 = lean::cnstr_get(x_31, 0);
lean::inc(x_81);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_82 = x_31;
} else {
 lean::dec_ref(x_31);
 x_82 = lean::box(0);
}
x_83 = l_PersistentHashMap_isUnaryNode___rarg(x_81);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; uint8 x_86; obj* x_87; obj* x_88; 
lean::cnstr_set(x_10, 0, x_81);
x_84 = lean_array_set(x_29, x_8, x_10);
lean::dec(x_8);
x_85 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = 1;
x_87 = lean::box(x_86);
if (lean::is_scalar(x_82)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_82;
}
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set(x_88, 1, x_87);
return x_88;
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; 
lean::dec(x_82);
lean::dec(x_81);
lean::free_heap_obj(x_10);
x_89 = lean::cnstr_get(x_83, 0);
lean::inc(x_89);
lean::dec(x_83);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_92 = x_89;
} else {
 lean::dec_ref(x_89);
 x_92 = lean::box(0);
}
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean_array_set(x_29, x_8, x_93);
lean::dec(x_8);
x_95 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_96 = 1;
x_97 = lean::box(x_96);
if (lean::is_scalar(x_92)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_92;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
obj* x_99; obj* x_100; usize x_101; obj* x_102; obj* x_103; uint8 x_104; 
x_99 = lean::cnstr_get(x_10, 0);
lean::inc(x_99);
lean::dec(x_10);
x_100 = lean_array_set(x_4, x_8, x_9);
x_101 = x_2 >> x_5;
x_102 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_99, x_101, x_3);
x_103 = lean::cnstr_get(x_102, 1);
lean::inc(x_103);
x_104 = lean::unbox(x_103);
lean::dec(x_103);
if (x_104 == 0)
{
obj* x_105; uint8 x_106; obj* x_107; obj* x_108; 
lean::dec(x_100);
lean::dec(x_8);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_105 = x_102;
} else {
 lean::dec_ref(x_102);
 x_105 = lean::box(0);
}
x_106 = 0;
x_107 = lean::box(x_106);
if (lean::is_scalar(x_105)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_105;
}
lean::cnstr_set(x_108, 0, x_1);
lean::cnstr_set(x_108, 1, x_107);
return x_108;
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_109 = x_1;
} else {
 lean::dec_ref(x_1);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_102, 0);
lean::inc(x_110);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_111 = x_102;
} else {
 lean::dec_ref(x_102);
 x_111 = lean::box(0);
}
x_112 = l_PersistentHashMap_isUnaryNode___rarg(x_110);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_114; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; 
x_113 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_113, 0, x_110);
x_114 = lean_array_set(x_100, x_8, x_113);
lean::dec(x_8);
if (lean::is_scalar(x_109)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_109;
}
lean::cnstr_set(x_115, 0, x_114);
x_116 = 1;
x_117 = lean::box(x_116);
if (lean::is_scalar(x_111)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_111;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set(x_118, 1, x_117);
return x_118;
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; uint8 x_126; obj* x_127; obj* x_128; 
lean::dec(x_111);
lean::dec(x_110);
x_119 = lean::cnstr_get(x_112, 0);
lean::inc(x_119);
lean::dec(x_112);
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_119, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_119)) {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_122 = x_119;
} else {
 lean::dec_ref(x_119);
 x_122 = lean::box(0);
}
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_121);
x_124 = lean_array_set(x_100, x_8, x_123);
lean::dec(x_8);
if (lean::is_scalar(x_109)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_109;
}
lean::cnstr_set(x_125, 0, x_124);
x_126 = 1;
x_127 = lean::box(x_126);
if (lean::is_scalar(x_122)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_122;
}
lean::cnstr_set(x_128, 0, x_125);
lean::cnstr_set(x_128, 1, x_127);
return x_128;
}
}
}
}
default: 
{
uint8 x_129; obj* x_130; obj* x_131; 
lean::dec(x_8);
lean::dec(x_4);
x_129 = 0;
x_130 = lean::box(x_129);
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_1);
lean::cnstr_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_132 = lean::cnstr_get(x_1, 0);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_1, 1);
lean::inc(x_133);
x_134 = lean::mk_nat_obj(0u);
x_135 = l_Array_indexOfAux___main___at_Lean_LocalContext_erase___spec__3(x_132, x_3, x_134);
if (lean::obj_tag(x_135) == 0)
{
uint8 x_136; obj* x_137; obj* x_138; 
lean::dec(x_133);
lean::dec(x_132);
x_136 = 0;
x_137 = lean::box(x_136);
x_138 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_138, 0, x_1);
lean::cnstr_set(x_138, 1, x_137);
return x_138;
}
else
{
uint8 x_139; 
x_139 = !lean::is_exclusive(x_1);
if (x_139 == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; uint8 x_145; obj* x_146; obj* x_147; 
x_140 = lean::cnstr_get(x_1, 1);
lean::dec(x_140);
x_141 = lean::cnstr_get(x_1, 0);
lean::dec(x_141);
x_142 = lean::cnstr_get(x_135, 0);
lean::inc(x_142);
lean::dec(x_135);
x_143 = l_Array_eraseIdx_x27___rarg(x_132, x_142);
x_144 = l_Array_eraseIdx_x27___rarg(x_133, x_142);
lean::dec(x_142);
lean::cnstr_set(x_1, 1, x_144);
lean::cnstr_set(x_1, 0, x_143);
x_145 = 1;
x_146 = lean::box(x_145);
x_147 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_147, 0, x_1);
lean::cnstr_set(x_147, 1, x_146);
return x_147;
}
else
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; uint8 x_152; obj* x_153; obj* x_154; 
lean::dec(x_1);
x_148 = lean::cnstr_get(x_135, 0);
lean::inc(x_148);
lean::dec(x_135);
x_149 = l_Array_eraseIdx_x27___rarg(x_132, x_148);
x_150 = l_Array_eraseIdx_x27___rarg(x_133, x_148);
lean::dec(x_148);
x_151 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_151, 0, x_149);
lean::cnstr_set(x_151, 1, x_150);
x_152 = 1;
x_153 = lean::box(x_152);
x_154 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_154, 0, x_151);
lean::cnstr_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
obj* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; usize x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean_name_hash_usize(x_2);
x_7 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_4, x_6, x_2);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
lean::cnstr_set(x_1, 0, x_10);
return x_1;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean::dec(x_5);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_11);
return x_1;
}
}
else
{
obj* x_14; obj* x_15; usize x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_16 = lean_name_hash_usize(x_2);
x_17 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_14, x_16, x_2);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_15);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean_nat_sub(x_15, x_23);
lean::dec(x_15);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
}
obj* lean_metavar_ctx_erase_delayed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 3);
x_5 = l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(x_4, x_2);
lean::dec(x_2);
lean::cnstr_set(x_1, 3, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_10 = l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(x_9, x_2);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_10);
return x_11;
}
}
}
obj* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
return x_5;
}
}
obj* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_lean_localcontext(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_metavarcontext(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_localcontext(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_MetavarContext_mkMetavarContext___closed__1 = _init_l_Lean_MetavarContext_mkMetavarContext___closed__1();
lean::mark_persistent(l_Lean_MetavarContext_mkMetavarContext___closed__1);
return w;
}
}
