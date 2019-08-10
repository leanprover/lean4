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
namespace lean {
uint8 metavar_ctx_is_level_assigned(obj*, obj*);
}
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(obj*, usize, obj*);
usize l_USize_mul(usize, usize);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_findDecl___spec__1(obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getDelayedAssignment___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2___boxed(obj*, obj*, obj*);
usize l_USize_shift__right(usize, usize);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_mkDecl___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isLevelAssigned___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_findDecl___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignLevel___spec__1(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3___boxed(obj*, obj*, obj*);
namespace lean {
obj* metavar_ctx_get_delayed_assignment_core(obj*, obj*);
}
usize l_USize_sub(usize, usize);
obj* l_PersistentHashMap_contains___main___at_Lean_MetavarContext_istDelayedAssigned___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2(obj*, usize, obj*);
namespace lean {
obj* metavar_ctx_get_expr_assignment_core(obj*, obj*);
}
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getExprAssignment___spec__1(obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isLevelAssigned___spec__1(obj*, obj*);
namespace lean {
uint8 metavar_ctx_is_delayed_assigned(obj*, obj*);
}
uint8 l_PersistentHashMap_contains___main___at_Lean_MetavarContext_istDelayedAssigned___spec__1(obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mkCollisionNode___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(obj*, obj*, obj*, obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getDelayedAssignment___spec__1___boxed(obj*, obj*);
usize l_USize_add(usize, usize);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
uint8 l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isExprAssigned___spec__1(obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(obj*, obj*, obj*, obj*, obj*);
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(obj*, usize, obj*);
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_mkDecl___spec__1(obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignLevel___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* metavar_ctx_assign_expr_core(obj*, obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(usize, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_mkDecl___spec__3(obj*, obj*, obj*, obj*);
extern usize l_PersistentHashMap_insertAux___main___rarg___closed__2;
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignDelayed___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignDelayed___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2___boxed(obj*, obj*, obj*);
namespace lean {
obj* metavar_ctx_get_level_assignment_core(obj*, obj*);
}
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(obj*, usize, usize, obj*, obj*);
uint8 l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(obj*, usize, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_MetavarContext_isLevelAssigned___boxed(obj*, obj*);
extern obj* l_PersistentHashMap_insertAux___main___rarg___closed__3;
obj* l_Array_size(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
namespace lean {
uint8 metavar_ctx_is_expr_assigned(obj*, obj*);
}
obj* l_Array_get(obj*, obj*, obj*, obj*);
namespace lean {
obj* metavar_ctx_mk_decl_core(obj*, obj*, obj*, obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_MetavarContext_assignExpr___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(obj*, usize, usize, obj*, obj*);
namespace lean {
obj* metavar_ctx_find_decl_core(obj*, obj*);
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignExpr___spec__1(obj*, obj*, obj*);
obj* l_Lean_MetavarContext_isExprAssigned___boxed(obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___main___rarg(obj*);
obj* l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isExprAssigned___spec__1___boxed(obj*, obj*);
namespace lean {
obj* metavar_ctx_assign_delayed_core(obj*, obj*, obj*, obj*, obj*);
}
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(obj*, usize, usize, obj*, obj*);
uint8 l_USize_decLe(usize, usize);
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getLevelAssignment___spec__1(obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getExprAssignment___spec__1___boxed(obj*, obj*);
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(obj*, usize, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(obj*, usize, obj*);
usize l_USize_land(usize, usize);
namespace lean {
obj* usize_to_nat(usize);
}
namespace lean {
obj* metavar_ctx_assign_level_core(obj*, obj*, obj*);
}
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getLevelAssignment___spec__1___boxed(obj*, obj*);
obj* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(obj*, usize, obj*);
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(obj*, usize, usize, obj*, obj*);
obj* l_Lean_MetavarContext_istDelayedAssigned___boxed(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_mkDecl___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_2, x_7);
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
x_12 = lean::array_push(x_5, x_3);
x_13 = lean::array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean::array_push(x_5, x_3);
x_15 = lean::array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_2, x_19);
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
x_25 = lean::array_fset(x_5, x_2, x_3);
x_26 = lean::array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean::array_fset(x_5, x_2, x_3);
x_28 = lean::array_fset(x_6, x_2, x_4);
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
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean::array_fget(x_4, x_5);
x_10 = 1;
x_11 = x_1 - x_10;
x_12 = 5;
x_13 = x_12 * x_11;
x_14 = lean_name_hash_usize(x_9);
x_15 = x_14 >> x_13;
x_16 = lean::array_fget(x_3, x_5);
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_mkDecl___spec__2(x_6, x_15, x_1, x_9, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_5, x_18);
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
x_12 = lean::usize_to_nat(x_11);
x_13 = lean::array_get_size(x_7);
x_14 = lean::nat_dec_lt(x_12, x_13);
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
x_15 = lean::array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean::array_fset(x_7, x_12, x_16);
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
x_24 = lean::array_fset(x_17, x_12, x_23);
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
x_25 = lean::array_fset(x_17, x_12, x_15);
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
x_31 = lean::array_fset(x_17, x_12, x_30);
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
x_33 = lean::array_fset(x_17, x_12, x_32);
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
x_39 = lean::array_fset(x_17, x_12, x_15);
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
x_45 = lean::array_fset(x_17, x_12, x_44);
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
x_47 = lean::array_fset(x_17, x_12, x_46);
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
x_53 = lean::usize_to_nat(x_52);
x_54 = lean::array_get_size(x_48);
x_55 = lean::nat_dec_lt(x_53, x_54);
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
x_57 = lean::array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean::array_fset(x_48, x_53, x_58);
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
x_66 = lean::array_fset(x_59, x_53, x_65);
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
x_69 = lean::array_fset(x_59, x_53, x_68);
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
x_77 = lean::array_fset(x_59, x_53, x_76);
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
x_80 = lean::array_fset(x_59, x_53, x_79);
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
x_86 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean::nat_dec_lt(x_86, x_87);
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
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_mkDecl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
x_11 = lean::nat_add(x_6, x_10);
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
x_18 = lean::nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
namespace lean {
obj* metavar_ctx_mk_decl_core(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_9 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_mkDecl___spec__1(x_7, x_2, x_8);
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
x_15 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_mkDecl___spec__1(x_10, x_2, x_14);
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_13);
return x_16;
}
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
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_4, x_6);
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
x_9 = lean::array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::array_fget(x_2, x_4);
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
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_findDecl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
obj* metavar_ctx_find_decl_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_findDecl___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_findDecl___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_findDecl___spec__1(x_1, x_2);
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
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_2, x_7);
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
x_12 = lean::array_push(x_5, x_3);
x_13 = lean::array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean::array_push(x_5, x_3);
x_15 = lean::array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_2, x_19);
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
x_25 = lean::array_fset(x_5, x_2, x_3);
x_26 = lean::array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean::array_fset(x_5, x_2, x_3);
x_28 = lean::array_fset(x_6, x_2, x_4);
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
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean::array_fget(x_4, x_5);
x_10 = 1;
x_11 = x_1 - x_10;
x_12 = 5;
x_13 = x_12 * x_11;
x_14 = lean_name_hash_usize(x_9);
x_15 = x_14 >> x_13;
x_16 = lean::array_fget(x_3, x_5);
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_6, x_15, x_1, x_9, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_5, x_18);
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
x_12 = lean::usize_to_nat(x_11);
x_13 = lean::array_get_size(x_7);
x_14 = lean::nat_dec_lt(x_12, x_13);
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
x_15 = lean::array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean::array_fset(x_7, x_12, x_16);
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
x_24 = lean::array_fset(x_17, x_12, x_23);
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
x_25 = lean::array_fset(x_17, x_12, x_15);
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
x_31 = lean::array_fset(x_17, x_12, x_30);
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
x_33 = lean::array_fset(x_17, x_12, x_32);
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
x_39 = lean::array_fset(x_17, x_12, x_15);
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
x_45 = lean::array_fset(x_17, x_12, x_44);
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
x_47 = lean::array_fset(x_17, x_12, x_46);
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
x_53 = lean::usize_to_nat(x_52);
x_54 = lean::array_get_size(x_48);
x_55 = lean::nat_dec_lt(x_53, x_54);
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
x_57 = lean::array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean::array_fset(x_48, x_53, x_58);
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
x_66 = lean::array_fset(x_59, x_53, x_65);
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
x_69 = lean::array_fset(x_59, x_53, x_68);
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
x_77 = lean::array_fset(x_59, x_53, x_76);
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
x_80 = lean::array_fset(x_59, x_53, x_79);
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
x_86 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean::nat_dec_lt(x_86, x_87);
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
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignLevel___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
x_11 = lean::nat_add(x_6, x_10);
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
x_18 = lean::nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
namespace lean {
obj* metavar_ctx_assign_level_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignLevel___spec__1(x_5, x_2, x_3);
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
x_11 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignLevel___spec__1(x_8, x_2, x_3);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_9);
lean::cnstr_set(x_12, 3, x_10);
return x_12;
}
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
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_2, x_7);
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
x_12 = lean::array_push(x_5, x_3);
x_13 = lean::array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean::array_push(x_5, x_3);
x_15 = lean::array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_2, x_19);
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
x_25 = lean::array_fset(x_5, x_2, x_3);
x_26 = lean::array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean::array_fset(x_5, x_2, x_3);
x_28 = lean::array_fset(x_6, x_2, x_4);
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
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean::array_fget(x_4, x_5);
x_10 = 1;
x_11 = x_1 - x_10;
x_12 = 5;
x_13 = x_12 * x_11;
x_14 = lean_name_hash_usize(x_9);
x_15 = x_14 >> x_13;
x_16 = lean::array_fget(x_3, x_5);
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_6, x_15, x_1, x_9, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_5, x_18);
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
x_12 = lean::usize_to_nat(x_11);
x_13 = lean::array_get_size(x_7);
x_14 = lean::nat_dec_lt(x_12, x_13);
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
x_15 = lean::array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean::array_fset(x_7, x_12, x_16);
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
x_24 = lean::array_fset(x_17, x_12, x_23);
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
x_25 = lean::array_fset(x_17, x_12, x_15);
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
x_31 = lean::array_fset(x_17, x_12, x_30);
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
x_33 = lean::array_fset(x_17, x_12, x_32);
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
x_39 = lean::array_fset(x_17, x_12, x_15);
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
x_45 = lean::array_fset(x_17, x_12, x_44);
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
x_47 = lean::array_fset(x_17, x_12, x_46);
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
x_53 = lean::usize_to_nat(x_52);
x_54 = lean::array_get_size(x_48);
x_55 = lean::nat_dec_lt(x_53, x_54);
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
x_57 = lean::array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean::array_fset(x_48, x_53, x_58);
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
x_66 = lean::array_fset(x_59, x_53, x_65);
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
x_69 = lean::array_fset(x_59, x_53, x_68);
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
x_77 = lean::array_fset(x_59, x_53, x_76);
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
x_80 = lean::array_fset(x_59, x_53, x_79);
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
x_86 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean::nat_dec_lt(x_86, x_87);
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
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignExpr___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
x_11 = lean::nat_add(x_6, x_10);
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
x_18 = lean::nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
namespace lean {
obj* metavar_ctx_assign_expr_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 2);
x_6 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignExpr___spec__1(x_5, x_2, x_3);
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
x_11 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignExpr___spec__1(x_9, x_2, x_3);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 2, x_11);
lean::cnstr_set(x_12, 3, x_10);
return x_12;
}
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
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_2, x_7);
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
x_12 = lean::array_push(x_5, x_3);
x_13 = lean::array_push(x_6, x_4);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_12);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean::array_push(x_5, x_3);
x_15 = lean::array_push(x_6, x_4);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::array_fget(x_5, x_2);
x_18 = lean_name_dec_eq(x_3, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_2, x_19);
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
x_25 = lean::array_fset(x_5, x_2, x_3);
x_26 = lean::array_fset(x_6, x_2, x_4);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_27 = lean::array_fset(x_5, x_2, x_3);
x_28 = lean::array_fset(x_6, x_2, x_4);
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
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
return x_6;
}
else
{
obj* x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean::array_fget(x_4, x_5);
x_10 = 1;
x_11 = x_1 - x_10;
x_12 = 5;
x_13 = x_12 * x_11;
x_14 = lean_name_hash_usize(x_9);
x_15 = x_14 >> x_13;
x_16 = lean::array_fget(x_3, x_5);
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_6, x_15, x_1, x_9, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_5, x_18);
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
x_12 = lean::usize_to_nat(x_11);
x_13 = lean::array_get_size(x_7);
x_14 = lean::nat_dec_lt(x_12, x_13);
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
x_15 = lean::array_fget(x_7, x_12);
x_16 = lean::box(2);
x_17 = lean::array_fset(x_7, x_12, x_16);
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
x_24 = lean::array_fset(x_17, x_12, x_23);
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
x_25 = lean::array_fset(x_17, x_12, x_15);
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
x_31 = lean::array_fset(x_17, x_12, x_30);
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
x_33 = lean::array_fset(x_17, x_12, x_32);
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
x_39 = lean::array_fset(x_17, x_12, x_15);
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
x_45 = lean::array_fset(x_17, x_12, x_44);
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
x_47 = lean::array_fset(x_17, x_12, x_46);
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
x_53 = lean::usize_to_nat(x_52);
x_54 = lean::array_get_size(x_48);
x_55 = lean::nat_dec_lt(x_53, x_54);
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
x_57 = lean::array_fget(x_48, x_53);
x_58 = lean::box(2);
x_59 = lean::array_fset(x_48, x_53, x_58);
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
x_66 = lean::array_fset(x_59, x_53, x_65);
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
x_69 = lean::array_fset(x_59, x_53, x_68);
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
x_77 = lean::array_fset(x_59, x_53, x_76);
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
x_80 = lean::array_fset(x_59, x_53, x_79);
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
x_86 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_83);
x_87 = lean::mk_nat_obj(4u);
x_88 = lean::nat_dec_lt(x_86, x_87);
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
obj* l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignDelayed___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
x_11 = lean::nat_add(x_6, x_10);
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
x_18 = lean::nat_add(x_13, x_17);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
namespace lean {
obj* metavar_ctx_assign_delayed_core(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_9 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignDelayed___spec__1(x_7, x_2, x_8);
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
x_15 = l_PersistentHashMap_insert___main___at_Lean_MetavarContext_assignDelayed___spec__1(x_13, x_2, x_14);
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_15);
return x_16;
}
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
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_4, x_6);
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
x_9 = lean::array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::array_fget(x_2, x_4);
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
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getLevelAssignment___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
obj* metavar_ctx_get_level_assignment_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_getLevelAssignment___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getLevelAssignment___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_getLevelAssignment___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_4, x_6);
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
x_9 = lean::array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::array_fget(x_2, x_4);
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
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getExprAssignment___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
obj* metavar_ctx_get_expr_assignment_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_getExprAssignment___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getExprAssignment___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_getExprAssignment___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_4, x_6);
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
x_9 = lean::array_fget(x_1, x_4);
x_10 = lean_name_dec_eq(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_3 = lean::box(0);
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::array_fget(x_2, x_4);
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
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getDelayedAssignment___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
obj* metavar_ctx_get_delayed_assignment_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 3);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_getDelayedAssignment___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_PersistentHashMap_find___main___at_Lean_MetavarContext_getDelayedAssignment___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_find___main___at_Lean_MetavarContext_getDelayedAssignment___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
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
x_7 = lean::array_fget(x_1, x_2);
x_8 = lean_name_dec_eq(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_2, x_9);
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
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
uint8 l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isLevelAssigned___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
uint8 metavar_ctx_is_level_assigned(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isLevelAssigned___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isLevelAssigned___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isLevelAssigned___spec__1(x_1, x_2);
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
x_3 = lean::metavar_ctx_is_level_assigned(x_1, x_2);
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
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
uint8 l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isExprAssigned___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
uint8 metavar_ctx_is_expr_assigned(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isExprAssigned___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isExprAssigned___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_PersistentHashMap_contains___main___at_Lean_MetavarContext_isExprAssigned___spec__1(x_1, x_2);
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
x_3 = lean::metavar_ctx_is_expr_assigned(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2(obj* x_1, usize x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; usize x_5; usize x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean::usize_to_nat(x_7);
x_9 = lean::box(2);
x_10 = lean::array_get(x_9, x_4, x_8);
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
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2(x_13, x_14, x_3);
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
uint8 l_PersistentHashMap_contains___main___at_Lean_MetavarContext_istDelayedAssigned___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_hash_usize(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
namespace lean {
uint8 metavar_ctx_is_delayed_assigned(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 3);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_PersistentHashMap_contains___main___at_Lean_MetavarContext_istDelayedAssigned___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
}
obj* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_istDelayedAssigned___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_PersistentHashMap_contains___main___at_Lean_MetavarContext_istDelayedAssigned___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_PersistentHashMap_contains___main___at_Lean_MetavarContext_istDelayedAssigned___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_MetavarContext_istDelayedAssigned___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::metavar_ctx_is_delayed_assigned(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_localcontext(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_metavarcontext(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_localcontext(w);
if (io_result_is_error(w)) return w;
return w;
}
