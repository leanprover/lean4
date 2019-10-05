// Lean compiler output
// Module: Init.Lean.TypeClass.Context
// Imports: Init.Data.PersistentArray.Default Init.Lean.Expr Init.Lean.MetavarContext
#include "runtime/lean.h"
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
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_slowWhnf(lean_object*);
uint8_t l_Lean_TypeClass_Context_eHasETmpMVar(lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasTmpMVar___closed__1;
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uMetaIdx(lean_object*);
lean_object* l_Lean_Expr_constName(lean_object*);
lean_object* l_Lean_TypeClass_Context_eOccursIn___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eLookupIdx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context__u03b1Norm___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer(lean_object*, lean_object*);
lean_object* l_Array_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx(lean_object*);
lean_object* l_Lean_TypeClass_Context_eMetaIdx(lean_object*);
extern lean_object* l_Lean_exprIsInhabited;
lean_object* l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAssignIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
size_t l_USize_shift__right(size_t, size_t);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context__u03b1Norm(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1;
lean_object* l_Lean_TypeClass_Context_slowWhnfApp(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uLookupIdx(lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* lean_expr_mk_pi(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify___main___closed__4;
uint8_t l_Lean_TypeClass_Context_eFind(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar___main(lean_object*);
lean_object* level_mk_mvar(lean_object*);
lean_object* l_Lean_TypeClass_Context_eFind___main___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInferIdx(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody(lean_object*);
lean_object* l_Lean_TypeClass_Context_uInstantiate___boxed(lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Lean_TypeClass_Context_eShallowInstantiate(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_metaPrefix___closed__1;
uint8_t l_Lean_TypeClass_Context_uFind(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
uint8_t l_Lean_TypeClass_Context_eOccursIn(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eAssign___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uNewMeta(lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify___main___closed__3;
lean_object* l_Lean_TypeClass_Context_eAssign(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uMetaIdx___boxed(lean_object*);
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_TypeClass_Context_uShallowInstantiate(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_Context_eAssign___closed__1;
lean_object* l_List_foldl___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l_Lean_TypeClass_Context_uLookupIdx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main___closed__1;
lean_object* l_Lean_TypeClass_Context_uFind___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eAlphaNormalizeCore(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_EState_fromState___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasTmpMVar___boxed(lean_object*);
lean_object* l_Lean_TypeClass_Context_slowWhnf___main___boxed(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_PUnit_Inhabited;
uint8_t l_Lean_TypeClass_Context_uIsMeta(lean_object*);
lean_object* l_Lean_TypeClass_Context_Inhabited;
uint8_t l_Lean_TypeClass_Context_uFind___main(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
uint8_t l_Lean_TypeClass_Context_eFind___main(lean_object*, lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eIsMeta___boxed(lean_object*);
uint8_t lean_level_eqv(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uIsMeta___boxed(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uInstantiate___main___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_TypeClass_Context_eInstantiate___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify___main___closed__1;
lean_object* l_Lean_LevelToFormat_Level_format(lean_object*);
lean_object* l_Lean_Expr_bindingDomain(lean_object*);
lean_object* l_Lean_TypeClass_Context_uHasTmpMVar___closed__1;
lean_object* l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eOccursIn___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasETmpMVar___closed__1;
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAssign___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TypeClass_Context_eHasTmpMVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_slowWhnf___boxed(lean_object*);
lean_object* l_Lean_TypeClass_Context_eInstantiate(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eMetaIdx___boxed(lean_object*);
lean_object* l_Lean_TypeClass_Context_eAssignIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1(uint8_t, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main___closed__2;
lean_object* l_Lean_TypeClass_Context_alphaMetaPrefix___closed__2;
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2(lean_object*, size_t, size_t);
lean_object* l_Lean_TypeClass_Context_eAssignIdx(lean_object*, lean_object*, lean_object*);
lean_object* level_mk_imax(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2(lean_object*, size_t, size_t);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uOccursIn___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_mvar(lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasETmpMVar___boxed(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer___closed__1;
lean_object* level_mk_succ(lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInstantiate___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAssignIdx(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uInstantiate___main(lean_object*, lean_object*);
uint8_t l_Lean_TypeClass_Context_uOccursIn(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer___closed__2;
uint8_t l_Lean_TypeClass_Context_uOccursIn___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Array_toPersistentArray___rarg___closed__1;
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_TypeClass_Context_uHasTmpMVar(lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_metaPrefix;
uint8_t l_Lean_TypeClass_Context_eIsMeta(lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
lean_object* l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eLookupIdx(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uFind___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels(lean_object*);
lean_object* l_Lean_TypeClass_Context_eInferIdx___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_metaPrefix___closed__2;
lean_object* l_Lean_TypeClass_Context_eFind___boxed(lean_object*, lean_object*);
uint8_t lean_expr_has_mvar(lean_object*);
uint8_t l_Lean_TypeClass_Context_eOccursIn___lambda__1(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_expr_mk_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eNewMeta(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uHasTmpMVar___boxed(lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___closed__1;
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__2;
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_uLookupIdx___spec__2(lean_object*, size_t, size_t);
lean_object* l_Lean_TypeClass_Context_uAssign(lean_object*, lean_object*, lean_object*);
size_t l_USize_shift__left(size_t, size_t);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_TypeClass_Context_uAlphaNormalizeCore(lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_uLookupIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarName(lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_TypeClass_Context_slowWhnf___main(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_TypeClass_Context_uOccursIn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uInstantiate(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify___main___closed__2;
uint8_t l_Lean_TypeClass_Context_eHasTmpMVar___lambda__1(lean_object*);
lean_object* l_EState_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasTmpMVar___lambda__1___boxed(lean_object*);
lean_object* l_List_mmap___main___at_Lean_TypeClass_Context_eAlphaNormalizeCore___main___spec__1(lean_object*, lean_object*);
lean_object* level_mk_max(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAssign___closed__1;
lean_object* l_Lean_TypeClass_Context_uUnify___main___closed__5;
lean_object* _init_l_Lean_TypeClass_Context_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_toPersistentArray___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_TypeClass_Context_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_Context_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_metaPrefix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tc_meta");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_metaPrefix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TypeClass_Context_metaPrefix___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_Context_metaPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_Context_metaPrefix___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tc_alpha");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_alphaMetaPrefix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_Context_alphaMetaPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_Context_alphaMetaPrefix___closed__2;
return x_1;
}
}
lean_object* l_Lean_TypeClass_Context_eMetaIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_TypeClass_Context_metaPrefix;
x_6 = lean_name_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
lean_object* l_Lean_TypeClass_Context_eMetaIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_eMetaIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_TypeClass_Context_eIsMeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_eMetaIdx(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 1;
return x_4;
}
}
}
lean_object* l_Lean_TypeClass_Context_eIsMeta___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Context_eIsMeta(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eNewMeta(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = l_PersistentArray_push___rarg(x_4, x_1);
x_8 = lean_box(0);
x_9 = l_PersistentArray_push___rarg(x_5, x_8);
lean_ctor_set(x_2, 2, x_9);
lean_ctor_set(x_2, 1, x_7);
x_10 = l_Lean_TypeClass_Context_metaPrefix;
x_11 = lean_name_mk_numeral(x_10, x_6);
x_12 = lean_expr_mk_mvar(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = l_PersistentArray_push___rarg(x_15, x_1);
x_19 = lean_box(0);
x_20 = l_PersistentArray_push___rarg(x_16, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_TypeClass_Context_metaPrefix;
x_23 = lean_name_mk_numeral(x_22, x_17);
x_24 = lean_expr_mk_mvar(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_PersistentArray_getAux___main___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_usize_to_nat(x_2);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_nat_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_9 = l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2(x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_nat_sub(x_2, x_4);
lean_dec(x_4);
x_12 = lean_array_get(x_3, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_Lean_TypeClass_Context_eLookupIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eLookupIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eLookupIdx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eShallowInstantiate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eMetaIdx(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1(x_6, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_PersistentArray_getAux___main___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_usize_to_nat(x_2);
x_18 = l_Lean_exprIsInhabited;
x_19 = lean_array_get(x_18, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_usize_of_nat(x_2);
x_7 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_8 = l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_11 = l_Lean_exprIsInhabited;
x_12 = lean_array_get(x_11, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
}
lean_object* l_Lean_TypeClass_Context_eInferIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eInferIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eInferIdx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_panicWithPos___rarg___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_panicWithPos___rarg___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_2);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_panicWithPos___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_repr(x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_panicWithPos___rarg___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_4);
x_18 = l_Lean_exprIsInhabited;
x_19 = lean_panic_fn(x_17);
return x_19;
}
}
lean_object* _init_l_Lean_TypeClass_Context_eInfer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/home/leonardo/projects/lean4/library/Init/Lean/TypeClass/Context.lean");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_eInfer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eInfer called on non-(tmp-)mvar");
return x_1;
}
}
lean_object* l_Lean_TypeClass_Context_eInfer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eMetaIdx(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_4 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_5 = lean_unsigned_to_nat(69u);
x_6 = lean_unsigned_to_nat(14u);
x_7 = l_Lean_TypeClass_Context_eInfer___closed__2;
x_8 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1(x_10, x_9);
lean_dec(x_9);
return x_11;
}
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_TypeClass_Context_eInfer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eInfer(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eAssignIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_PersistentArray_set___rarg(x_5, x_1, x_6);
lean_ctor_set(x_3, 2, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_PersistentArray_set___rarg(x_12, x_1, x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Lean_TypeClass_Context_eAssignIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_eAssignIdx(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_Monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__1;
x_2 = l_PUnit_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_4);
x_19 = l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__2;
x_20 = lean_panic_fn(x_18);
x_21 = lean_apply_1(x_20, x_5);
return x_21;
}
}
lean_object* _init_l_Lean_TypeClass_Context_eAssign___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eAssign called on non-(tmp-)mvar");
return x_1;
}
}
lean_object* l_Lean_TypeClass_Context_eAssign(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_eMetaIdx(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_6 = lean_unsigned_to_nat(77u);
x_7 = lean_unsigned_to_nat(14u);
x_8 = l_Lean_TypeClass_Context_eAssign___closed__1;
x_9 = l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1(x_5, x_6, x_7, x_8, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_3, 2);
lean_ctor_set(x_4, 0, x_2);
x_14 = l_PersistentArray_set___rarg(x_13, x_12, x_4);
lean_dec(x_12);
lean_ctor_set(x_3, 2, x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_ctor_set(x_4, 0, x_2);
x_21 = l_PersistentArray_set___rarg(x_20, x_17, x_4);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_29 = x_3;
} else {
 lean_dec_ref(x_3);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_PersistentArray_set___rarg(x_28, x_25, x_30);
lean_dec(x_25);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 3, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_TypeClass_Context_eAssign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_eAssign(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
uint8_t l_Lean_TypeClass_Context_eFind___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_Lean_TypeClass_Context_eFind___main(x_1, x_5);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = 1;
return x_9;
}
}
case 7:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_TypeClass_Context_eFind___main(x_1, x_10);
if (x_12 == 0)
{
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = 1;
return x_14;
}
}
default: 
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
}
lean_object* l_Lean_TypeClass_Context_eFind___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_eFind___main(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_TypeClass_Context_eFind(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_TypeClass_Context_eFind___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eFind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_eFind(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_TypeClass_Context_eOccursIn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
uint8_t l_Lean_TypeClass_Context_eOccursIn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eOccursIn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_TypeClass_Context_eFind___main(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_eOccursIn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_eOccursIn___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_eOccursIn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_eOccursIn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_TypeClass_Context_eHasETmpMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eIsMeta___boxed), 1, 0);
return x_1;
}
}
uint8_t l_Lean_TypeClass_Context_eHasETmpMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_TypeClass_Context_eHasETmpMVar___closed__1;
x_3 = l_Lean_TypeClass_Context_eFind___main(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eHasETmpMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Context_eHasETmpMVar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uMetaIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_TypeClass_Context_metaPrefix;
x_6 = lean_name_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
lean_object* l_Lean_TypeClass_Context_uMetaIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_uMetaIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_TypeClass_Context_uIsMeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_uMetaIdx(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 1;
return x_4;
}
}
}
lean_object* l_Lean_TypeClass_Context_uIsMeta___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Context_uIsMeta(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uNewMeta(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_PersistentArray_push___rarg(x_3, x_5);
lean_ctor_set(x_1, 0, x_6);
x_7 = l_Lean_TypeClass_Context_metaPrefix;
x_8 = lean_name_mk_numeral(x_7, x_4);
x_9 = level_mk_mvar(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = l_PersistentArray_push___rarg(x_11, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
x_18 = l_Lean_TypeClass_Context_metaPrefix;
x_19 = lean_name_mk_numeral(x_18, x_14);
x_20 = level_mk_mvar(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_uLookupIdx___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_PersistentArray_getAux___main___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_usize_to_nat(x_2);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_nat_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_9 = l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_uLookupIdx___spec__2(x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_nat_sub(x_2, x_4);
lean_dec(x_4);
x_12 = lean_array_get(x_3, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_Lean_TypeClass_Context_uLookupIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_uLookupIdx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_uLookupIdx___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uLookupIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uLookupIdx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uShallowInstantiate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uMetaIdx(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1(x_6, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_uAssignIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_PersistentArray_set___rarg(x_5, x_1, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_PersistentArray_set___rarg(x_10, x_1, x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Lean_TypeClass_Context_uAssignIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_uAssignIdx(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uAssign___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uassign called on non-(tmp-)mvar");
return x_1;
}
}
lean_object* l_Lean_TypeClass_Context_uAssign(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_uMetaIdx(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_6 = lean_unsigned_to_nat(126u);
x_7 = lean_unsigned_to_nat(14u);
x_8 = l_Lean_TypeClass_Context_uAssign___closed__1;
x_9 = l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1(x_5, x_6, x_7, x_8, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_3, 0);
lean_ctor_set(x_4, 0, x_2);
x_14 = l_PersistentArray_set___rarg(x_13, x_12, x_4);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_ctor_set(x_4, 0, x_2);
x_21 = l_PersistentArray_set___rarg(x_18, x_17, x_4);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_29 = x_3;
} else {
 lean_dec_ref(x_3);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_PersistentArray_set___rarg(x_26, x_25, x_30);
lean_dec(x_25);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 3, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_uAssign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_uAssign(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
uint8_t l_Lean_TypeClass_Context_uFind___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
case 2:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_TypeClass_Context_uFind___main(x_1, x_7);
if (x_9 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
case 3:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_TypeClass_Context_uFind___main(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
default: 
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = 0;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 1;
return x_18;
}
}
}
lean_object* l_Lean_TypeClass_Context_uFind___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_uFind___main(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_TypeClass_Context_uFind(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_TypeClass_Context_uFind___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uFind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_uFind(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_TypeClass_Context_uOccursIn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_level_eqv(x_2, x_1);
return x_3;
}
}
uint8_t l_Lean_TypeClass_Context_uOccursIn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uOccursIn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_TypeClass_Context_uFind___main(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_uOccursIn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_uOccursIn___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_uOccursIn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_TypeClass_Context_uOccursIn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uHasTmpMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uIsMeta___boxed), 1, 0);
return x_1;
}
}
uint8_t l_Lean_TypeClass_Context_uHasTmpMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_TypeClass_Context_uHasTmpMVar___closed__1;
x_3 = l_Lean_TypeClass_Context_uFind___main(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uHasTmpMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Context_uHasTmpMVar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uUnify___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lUnify: ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uUnify___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" !=?= ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uUnify___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level.param clash");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uUnify___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level.mvar clash");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_uUnify___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("occurs");
return x_1;
}
}
lean_object* l_Lean_TypeClass_Context_uUnify___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uShallowInstantiate), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_EState_fromState___rarg(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uShallowInstantiate), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = l_EState_fromState___rarg(x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_122; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_ctor_set(x_10, 0, x_8);
x_122 = l_Lean_TypeClass_Context_uIsMeta(x_12);
if (x_122 == 0)
{
x_14 = x_8;
goto block_121;
}
else
{
uint8_t x_123; 
x_123 = l_Lean_TypeClass_Context_uIsMeta(x_7);
if (x_123 == 0)
{
lean_dec(x_13);
x_1 = x_12;
x_2 = x_7;
x_3 = x_10;
goto _start;
}
else
{
x_14 = x_8;
goto block_121;
}
}
block_121:
{
lean_dec(x_14);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = l_Lean_LevelToFormat_Level_format(x_7);
x_17 = l_Lean_Options_empty;
x_18 = l_Lean_Format_pretty(x_16, x_17);
x_19 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_LevelToFormat_Level_format(x_12);
x_24 = l_Lean_Format_pretty(x_23, x_17);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
case 1:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_1 = x_27;
x_2 = x_28;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_10);
x_30 = l_Lean_LevelToFormat_Level_format(x_7);
x_31 = l_Lean_Options_empty;
x_32 = l_Lean_Format_pretty(x_30, x_31);
x_33 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lean_LevelToFormat_Level_format(x_12);
x_38 = l_Lean_Format_pretty(x_37, x_31);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_13);
return x_40;
}
}
case 2:
{
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_dec(x_12);
x_45 = l_Lean_TypeClass_Context_uUnify___main(x_41, x_43, x_10);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_8);
x_1 = x_42;
x_2 = x_44;
x_3 = x_45;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_49);
x_1 = x_42;
x_2 = x_44;
x_3 = x_50;
goto _start;
}
}
else
{
uint8_t x_52; 
lean_dec(x_44);
lean_dec(x_42);
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
x_56 = l_Lean_LevelToFormat_Level_format(x_7);
x_57 = l_Lean_Options_empty;
x_58 = l_Lean_Format_pretty(x_56, x_57);
x_59 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lean_LevelToFormat_Level_format(x_12);
x_64 = l_Lean_Format_pretty(x_63, x_57);
x_65 = lean_string_append(x_62, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_13);
return x_66;
}
}
case 3:
{
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_13);
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
lean_dec(x_7);
x_69 = lean_ctor_get(x_12, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_dec(x_12);
x_71 = l_Lean_TypeClass_Context_uUnify___main(x_67, x_69, x_10);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_8);
x_1 = x_68;
x_2 = x_70;
x_3 = x_71;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_8);
lean_ctor_set(x_76, 1, x_75);
x_1 = x_68;
x_2 = x_70;
x_3 = x_76;
goto _start;
}
}
else
{
uint8_t x_78; 
lean_dec(x_70);
lean_dec(x_68);
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_71, 0);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_71);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
x_82 = l_Lean_LevelToFormat_Level_format(x_7);
x_83 = l_Lean_Options_empty;
x_84 = l_Lean_Format_pretty(x_82, x_83);
x_85 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_88 = lean_string_append(x_86, x_87);
x_89 = l_Lean_LevelToFormat_Level_format(x_12);
x_90 = l_Lean_Format_pretty(x_89, x_83);
x_91 = lean_string_append(x_88, x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_13);
return x_92;
}
}
case 4:
{
lean_dec(x_10);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_7, 0);
lean_inc(x_93);
lean_dec(x_7);
x_94 = lean_ctor_get(x_12, 0);
lean_inc(x_94);
lean_dec(x_12);
x_95 = lean_name_dec_eq(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_TypeClass_Context_uUnify___main___closed__3;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_13);
return x_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_8);
lean_ctor_set(x_98, 1, x_13);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = l_Lean_LevelToFormat_Level_format(x_7);
x_100 = l_Lean_Options_empty;
x_101 = l_Lean_Format_pretty(x_99, x_100);
x_102 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_105 = lean_string_append(x_103, x_104);
x_106 = l_Lean_LevelToFormat_Level_format(x_12);
x_107 = l_Lean_Format_pretty(x_106, x_100);
x_108 = lean_string_append(x_105, x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_13);
return x_109;
}
}
default: 
{
lean_object* x_110; 
x_110 = l_Lean_TypeClass_Context_uMetaIdx(x_7);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_10);
x_111 = lean_level_eqv(x_7, x_12);
lean_dec(x_12);
lean_dec(x_7);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Lean_TypeClass_Context_uUnify___main___closed__4;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_13);
return x_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_8);
lean_ctor_set(x_114, 1, x_13);
return x_114;
}
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
lean_dec(x_110);
lean_inc(x_12);
x_116 = l_Lean_TypeClass_Context_uOccursIn(x_7, x_12);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_13);
x_117 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uAssignIdx___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_12);
x_118 = l_EState_fromState___rarg(x_117, x_10);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_115);
lean_dec(x_10);
lean_dec(x_12);
x_119 = l_Lean_TypeClass_Context_uUnify___main___closed__5;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_13);
return x_120;
}
}
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_232; 
x_125 = lean_ctor_get(x_10, 0);
x_126 = lean_ctor_get(x_10, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_10);
lean_inc(x_126);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_8);
lean_ctor_set(x_127, 1, x_126);
x_232 = l_Lean_TypeClass_Context_uIsMeta(x_125);
if (x_232 == 0)
{
x_128 = x_8;
goto block_231;
}
else
{
uint8_t x_233; 
x_233 = l_Lean_TypeClass_Context_uIsMeta(x_7);
if (x_233 == 0)
{
lean_dec(x_126);
x_1 = x_125;
x_2 = x_7;
x_3 = x_127;
goto _start;
}
else
{
x_128 = x_8;
goto block_231;
}
}
block_231:
{
lean_dec(x_128);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_dec(x_127);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_8);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = l_Lean_LevelToFormat_Level_format(x_7);
x_131 = l_Lean_Options_empty;
x_132 = l_Lean_Format_pretty(x_130, x_131);
x_133 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_136 = lean_string_append(x_134, x_135);
x_137 = l_Lean_LevelToFormat_Level_format(x_125);
x_138 = l_Lean_Format_pretty(x_137, x_131);
x_139 = lean_string_append(x_136, x_138);
lean_dec(x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
return x_140;
}
}
case 1:
{
if (lean_obj_tag(x_125) == 1)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_126);
x_141 = lean_ctor_get(x_7, 0);
lean_inc(x_141);
lean_dec(x_7);
x_142 = lean_ctor_get(x_125, 0);
lean_inc(x_142);
lean_dec(x_125);
x_1 = x_141;
x_2 = x_142;
x_3 = x_127;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_127);
x_144 = l_Lean_LevelToFormat_Level_format(x_7);
x_145 = l_Lean_Options_empty;
x_146 = l_Lean_Format_pretty(x_144, x_145);
x_147 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_149 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_150 = lean_string_append(x_148, x_149);
x_151 = l_Lean_LevelToFormat_Level_format(x_125);
x_152 = l_Lean_Format_pretty(x_151, x_145);
x_153 = lean_string_append(x_150, x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_126);
return x_154;
}
}
case 2:
{
if (lean_obj_tag(x_125) == 2)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_126);
x_155 = lean_ctor_get(x_7, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_7, 1);
lean_inc(x_156);
lean_dec(x_7);
x_157 = lean_ctor_get(x_125, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_125, 1);
lean_inc(x_158);
lean_dec(x_125);
x_159 = l_Lean_TypeClass_Context_uUnify___main(x_155, x_157, x_127);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
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
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_8);
lean_ctor_set(x_162, 1, x_160);
x_1 = x_156;
x_2 = x_158;
x_3 = x_162;
goto _start;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_158);
lean_dec(x_156);
x_164 = lean_ctor_get(x_159, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_159, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_166 = x_159;
} else {
 lean_dec_ref(x_159);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_127);
x_168 = l_Lean_LevelToFormat_Level_format(x_7);
x_169 = l_Lean_Options_empty;
x_170 = l_Lean_Format_pretty(x_168, x_169);
x_171 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_172 = lean_string_append(x_171, x_170);
lean_dec(x_170);
x_173 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_174 = lean_string_append(x_172, x_173);
x_175 = l_Lean_LevelToFormat_Level_format(x_125);
x_176 = l_Lean_Format_pretty(x_175, x_169);
x_177 = lean_string_append(x_174, x_176);
lean_dec(x_176);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_126);
return x_178;
}
}
case 3:
{
if (lean_obj_tag(x_125) == 3)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_126);
x_179 = lean_ctor_get(x_7, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_7, 1);
lean_inc(x_180);
lean_dec(x_7);
x_181 = lean_ctor_get(x_125, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_125, 1);
lean_inc(x_182);
lean_dec(x_125);
x_183 = l_Lean_TypeClass_Context_uUnify___main(x_179, x_181, x_127);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_8);
lean_ctor_set(x_186, 1, x_184);
x_1 = x_180;
x_2 = x_182;
x_3 = x_186;
goto _start;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_182);
lean_dec(x_180);
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_190 = x_183;
} else {
 lean_dec_ref(x_183);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_127);
x_192 = l_Lean_LevelToFormat_Level_format(x_7);
x_193 = l_Lean_Options_empty;
x_194 = l_Lean_Format_pretty(x_192, x_193);
x_195 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_196 = lean_string_append(x_195, x_194);
lean_dec(x_194);
x_197 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_198 = lean_string_append(x_196, x_197);
x_199 = l_Lean_LevelToFormat_Level_format(x_125);
x_200 = l_Lean_Format_pretty(x_199, x_193);
x_201 = lean_string_append(x_198, x_200);
lean_dec(x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_126);
return x_202;
}
}
case 4:
{
lean_dec(x_127);
if (lean_obj_tag(x_125) == 4)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_ctor_get(x_7, 0);
lean_inc(x_203);
lean_dec(x_7);
x_204 = lean_ctor_get(x_125, 0);
lean_inc(x_204);
lean_dec(x_125);
x_205 = lean_name_dec_eq(x_203, x_204);
lean_dec(x_204);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Lean_TypeClass_Context_uUnify___main___closed__3;
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_126);
return x_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_8);
lean_ctor_set(x_208, 1, x_126);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = l_Lean_LevelToFormat_Level_format(x_7);
x_210 = l_Lean_Options_empty;
x_211 = l_Lean_Format_pretty(x_209, x_210);
x_212 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_213 = lean_string_append(x_212, x_211);
lean_dec(x_211);
x_214 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_215 = lean_string_append(x_213, x_214);
x_216 = l_Lean_LevelToFormat_Level_format(x_125);
x_217 = l_Lean_Format_pretty(x_216, x_210);
x_218 = lean_string_append(x_215, x_217);
lean_dec(x_217);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_126);
return x_219;
}
}
default: 
{
lean_object* x_220; 
x_220 = l_Lean_TypeClass_Context_uMetaIdx(x_7);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
lean_dec(x_127);
x_221 = lean_level_eqv(x_7, x_125);
lean_dec(x_125);
lean_dec(x_7);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = l_Lean_TypeClass_Context_uUnify___main___closed__4;
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_126);
return x_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_8);
lean_ctor_set(x_224, 1, x_126);
return x_224;
}
}
else
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
lean_dec(x_220);
lean_inc(x_125);
x_226 = l_Lean_TypeClass_Context_uOccursIn(x_7, x_125);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_126);
x_227 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uAssignIdx___boxed), 3, 2);
lean_closure_set(x_227, 0, x_225);
lean_closure_set(x_227, 1, x_125);
x_228 = l_EState_fromState___rarg(x_227, x_127);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_225);
lean_dec(x_127);
lean_dec(x_125);
x_229 = l_Lean_TypeClass_Context_uUnify___main___closed__5;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_126);
return x_230;
}
}
}
}
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_7);
x_235 = !lean_is_exclusive(x_10);
if (x_235 == 0)
{
return x_10;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_10, 0);
x_237 = lean_ctor_get(x_10, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_10);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_5, 0);
x_240 = lean_ctor_get(x_5, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_5);
x_241 = lean_box(0);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uShallowInstantiate), 2, 1);
lean_closure_set(x_243, 0, x_2);
x_244 = l_EState_fromState___rarg(x_243, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_353; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
lean_inc(x_246);
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_241);
lean_ctor_set(x_248, 1, x_246);
x_353 = l_Lean_TypeClass_Context_uIsMeta(x_245);
if (x_353 == 0)
{
x_249 = x_241;
goto block_352;
}
else
{
uint8_t x_354; 
x_354 = l_Lean_TypeClass_Context_uIsMeta(x_239);
if (x_354 == 0)
{
lean_dec(x_246);
x_1 = x_245;
x_2 = x_239;
x_3 = x_248;
goto _start;
}
else
{
x_249 = x_241;
goto block_352;
}
}
block_352:
{
lean_dec(x_249);
switch (lean_obj_tag(x_239)) {
case 0:
{
lean_dec(x_248);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_241);
lean_ctor_set(x_250, 1, x_246);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_251 = l_Lean_LevelToFormat_Level_format(x_239);
x_252 = l_Lean_Options_empty;
x_253 = l_Lean_Format_pretty(x_251, x_252);
x_254 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_255 = lean_string_append(x_254, x_253);
lean_dec(x_253);
x_256 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_257 = lean_string_append(x_255, x_256);
x_258 = l_Lean_LevelToFormat_Level_format(x_245);
x_259 = l_Lean_Format_pretty(x_258, x_252);
x_260 = lean_string_append(x_257, x_259);
lean_dec(x_259);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_246);
return x_261;
}
}
case 1:
{
if (lean_obj_tag(x_245) == 1)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_246);
x_262 = lean_ctor_get(x_239, 0);
lean_inc(x_262);
lean_dec(x_239);
x_263 = lean_ctor_get(x_245, 0);
lean_inc(x_263);
lean_dec(x_245);
x_1 = x_262;
x_2 = x_263;
x_3 = x_248;
goto _start;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_248);
x_265 = l_Lean_LevelToFormat_Level_format(x_239);
x_266 = l_Lean_Options_empty;
x_267 = l_Lean_Format_pretty(x_265, x_266);
x_268 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_269 = lean_string_append(x_268, x_267);
lean_dec(x_267);
x_270 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_271 = lean_string_append(x_269, x_270);
x_272 = l_Lean_LevelToFormat_Level_format(x_245);
x_273 = l_Lean_Format_pretty(x_272, x_266);
x_274 = lean_string_append(x_271, x_273);
lean_dec(x_273);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_246);
return x_275;
}
}
case 2:
{
if (lean_obj_tag(x_245) == 2)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_246);
x_276 = lean_ctor_get(x_239, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_239, 1);
lean_inc(x_277);
lean_dec(x_239);
x_278 = lean_ctor_get(x_245, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_245, 1);
lean_inc(x_279);
lean_dec(x_245);
x_280 = l_Lean_TypeClass_Context_uUnify___main(x_276, x_278, x_248);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_241);
lean_ctor_set(x_283, 1, x_281);
x_1 = x_277;
x_2 = x_279;
x_3 = x_283;
goto _start;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_279);
lean_dec(x_277);
x_285 = lean_ctor_get(x_280, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_287 = x_280;
} else {
 lean_dec_ref(x_280);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_248);
x_289 = l_Lean_LevelToFormat_Level_format(x_239);
x_290 = l_Lean_Options_empty;
x_291 = l_Lean_Format_pretty(x_289, x_290);
x_292 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_293 = lean_string_append(x_292, x_291);
lean_dec(x_291);
x_294 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_295 = lean_string_append(x_293, x_294);
x_296 = l_Lean_LevelToFormat_Level_format(x_245);
x_297 = l_Lean_Format_pretty(x_296, x_290);
x_298 = lean_string_append(x_295, x_297);
lean_dec(x_297);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_246);
return x_299;
}
}
case 3:
{
if (lean_obj_tag(x_245) == 3)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_246);
x_300 = lean_ctor_get(x_239, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_239, 1);
lean_inc(x_301);
lean_dec(x_239);
x_302 = lean_ctor_get(x_245, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_245, 1);
lean_inc(x_303);
lean_dec(x_245);
x_304 = l_Lean_TypeClass_Context_uUnify___main(x_300, x_302, x_248);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_306 = x_304;
} else {
 lean_dec_ref(x_304);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_241);
lean_ctor_set(x_307, 1, x_305);
x_1 = x_301;
x_2 = x_303;
x_3 = x_307;
goto _start;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_303);
lean_dec(x_301);
x_309 = lean_ctor_get(x_304, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_311 = x_304;
} else {
 lean_dec_ref(x_304);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_248);
x_313 = l_Lean_LevelToFormat_Level_format(x_239);
x_314 = l_Lean_Options_empty;
x_315 = l_Lean_Format_pretty(x_313, x_314);
x_316 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_317 = lean_string_append(x_316, x_315);
lean_dec(x_315);
x_318 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_319 = lean_string_append(x_317, x_318);
x_320 = l_Lean_LevelToFormat_Level_format(x_245);
x_321 = l_Lean_Format_pretty(x_320, x_314);
x_322 = lean_string_append(x_319, x_321);
lean_dec(x_321);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_246);
return x_323;
}
}
case 4:
{
lean_dec(x_248);
if (lean_obj_tag(x_245) == 4)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_324 = lean_ctor_get(x_239, 0);
lean_inc(x_324);
lean_dec(x_239);
x_325 = lean_ctor_get(x_245, 0);
lean_inc(x_325);
lean_dec(x_245);
x_326 = lean_name_dec_eq(x_324, x_325);
lean_dec(x_325);
lean_dec(x_324);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = l_Lean_TypeClass_Context_uUnify___main___closed__3;
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_246);
return x_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_241);
lean_ctor_set(x_329, 1, x_246);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_330 = l_Lean_LevelToFormat_Level_format(x_239);
x_331 = l_Lean_Options_empty;
x_332 = l_Lean_Format_pretty(x_330, x_331);
x_333 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_334 = lean_string_append(x_333, x_332);
lean_dec(x_332);
x_335 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_336 = lean_string_append(x_334, x_335);
x_337 = l_Lean_LevelToFormat_Level_format(x_245);
x_338 = l_Lean_Format_pretty(x_337, x_331);
x_339 = lean_string_append(x_336, x_338);
lean_dec(x_338);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_246);
return x_340;
}
}
default: 
{
lean_object* x_341; 
x_341 = l_Lean_TypeClass_Context_uMetaIdx(x_239);
if (lean_obj_tag(x_341) == 0)
{
uint8_t x_342; 
lean_dec(x_248);
x_342 = lean_level_eqv(x_239, x_245);
lean_dec(x_245);
lean_dec(x_239);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = l_Lean_TypeClass_Context_uUnify___main___closed__4;
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_246);
return x_344;
}
else
{
lean_object* x_345; 
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_241);
lean_ctor_set(x_345, 1, x_246);
return x_345;
}
}
else
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_341, 0);
lean_inc(x_346);
lean_dec(x_341);
lean_inc(x_245);
x_347 = l_Lean_TypeClass_Context_uOccursIn(x_239, x_245);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_246);
x_348 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_uAssignIdx___boxed), 3, 2);
lean_closure_set(x_348, 0, x_346);
lean_closure_set(x_348, 1, x_245);
x_349 = l_EState_fromState___rarg(x_348, x_248);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_346);
lean_dec(x_248);
lean_dec(x_245);
x_350 = l_Lean_TypeClass_Context_uUnify___main___closed__5;
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_246);
return x_351;
}
}
}
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_239);
x_356 = lean_ctor_get(x_244, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_244, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_358 = x_244;
} else {
 lean_dec_ref(x_244);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
}
else
{
uint8_t x_360; 
lean_dec(x_2);
x_360 = !lean_is_exclusive(x_5);
if (x_360 == 0)
{
return x_5;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_5, 0);
x_362 = lean_ctor_get(x_5, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_5);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_uUnify(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_uUnify___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_uInstantiate___main(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Level_hasMVar___main(x_2);
if (x_3 == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_uMetaIdx(x_2);
if (lean_obj_tag(x_4) == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_5);
x_7 = level_mk_succ(x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_10 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_8);
x_11 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_9);
x_12 = level_mk_max(x_10, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_15 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_13);
x_16 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_14);
x_17 = level_mk_imax(x_15, x_16);
return x_17;
}
default: 
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_1);
x_19 = l_Lean_TypeClass_Context_uLookupIdx(x_18, x_1);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_21);
lean_dec(x_21);
return x_22;
}
}
}
}
}
lean_object* l_Lean_TypeClass_Context_uInstantiate___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uInstantiate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uInstantiate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uInstantiate(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1(x_1, x_4);
x_6 = l_Lean_TypeClass_Context_uHasTmpMVar___closed__1;
x_7 = l_Lean_TypeClass_Context_uFind___main(x_6, x_3);
if (x_7 == 0)
{
return x_5;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_Lean_TypeClass_Context_eHasTmpMVar___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_TypeClass_Context_eIsMeta(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConst(x_1);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_Expr_constLevels(x_1);
x_5 = 0;
x_6 = l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1(x_5, x_4);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
lean_object* _init_l_Lean_TypeClass_Context_eHasTmpMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eHasTmpMVar___lambda__1___boxed), 1, 0);
return x_1;
}
}
uint8_t l_Lean_TypeClass_Context_eHasTmpMVar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_expr_has_mvar(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_TypeClass_Context_eHasTmpMVar___closed__1;
x_5 = l_Lean_TypeClass_Context_eFind___main(x_4, x_1);
return x_5;
}
}
}
lean_object* l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_TypeClass_Context_eHasTmpMVar___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Context_eHasTmpMVar___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_eHasTmpMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Context_eHasTmpMVar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_mkApp___spec__1(x_1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_expr_instantiate1(x_4, x_5);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_9; 
x_9 = l_List_foldl___main___at_Lean_mkApp___spec__1(x_1, x_2);
return x_9;
}
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnfApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_slowWhnfApp___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnf___main(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isApp(x_1);
if (x_2 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Expr_getAppFn___main(x_1);
x_4 = l_Lean_TypeClass_Context_slowWhnf___main(x_3);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_getAppArgsAux___main(x_1, x_5);
x_7 = l_Lean_TypeClass_Context_slowWhnfApp___main(x_4, x_6);
return x_7;
}
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnf___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_slowWhnf___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_slowWhnf___main(x_1);
return x_2;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Context_slowWhnf(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Inhabited;
x_2 = lean_alloc_closure((void*)(l_EState_Inhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_4);
x_19 = l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___closed__1;
x_20 = lean_panic_fn(x_18);
x_21 = lean_apply_1(x_20, x_5);
return x_21;
}
}
lean_object* l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
x_4 = x_12;
goto block_11;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
x_4 = x_13;
goto block_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_TypeClass_Context_eUnify___main(x_14, x_16, x_3);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
x_1 = x_15;
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_1 = x_15;
x_2 = x_17;
x_3 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
block_11:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
lean_object* l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
x_4 = x_12;
goto block_11;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
x_4 = x_13;
goto block_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_TypeClass_Context_uUnify___main(x_14, x_16, x_3);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
x_1 = x_15;
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_1 = x_15;
x_2 = x_17;
x_3 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
block_11:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
lean_object* _init_l_Lean_TypeClass_Context_eUnify___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eUnify: ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Context_eUnify___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("UNREACHABLE");
return x_1;
}
}
lean_object* l_Lean_TypeClass_Context_eUnify___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_507; 
x_507 = lean_expr_has_mvar(x_1);
if (x_507 == 0)
{
uint8_t x_508; 
x_508 = lean_expr_has_mvar(x_2);
if (x_508 == 0)
{
uint8_t x_509; 
x_509 = lean_expr_eqv(x_1, x_2);
if (x_509 == 0)
{
uint8_t x_510; 
x_510 = !lean_is_exclusive(x_3);
if (x_510 == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_511 = lean_ctor_get(x_3, 0);
lean_dec(x_511);
x_512 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_513 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_514 = lean_string_append(x_513, x_512);
lean_dec(x_512);
x_515 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_516 = lean_string_append(x_514, x_515);
x_517 = lean_expr_dbg_to_string(x_2);
lean_dec(x_2);
x_518 = lean_string_append(x_516, x_517);
lean_dec(x_517);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_518);
return x_3;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_519 = lean_ctor_get(x_3, 1);
lean_inc(x_519);
lean_dec(x_3);
x_520 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_521 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_522 = lean_string_append(x_521, x_520);
lean_dec(x_520);
x_523 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_524 = lean_string_append(x_522, x_523);
x_525 = lean_expr_dbg_to_string(x_2);
lean_dec(x_2);
x_526 = lean_string_append(x_524, x_525);
lean_dec(x_525);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_519);
return x_527;
}
}
else
{
uint8_t x_528; 
lean_dec(x_2);
lean_dec(x_1);
x_528 = !lean_is_exclusive(x_3);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_ctor_get(x_3, 0);
lean_dec(x_529);
x_530 = lean_box(0);
lean_ctor_set(x_3, 0, x_530);
return x_3;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_3, 1);
lean_inc(x_531);
lean_dec(x_3);
x_532 = lean_box(0);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_531);
return x_533;
}
}
}
else
{
lean_object* x_534; 
x_534 = lean_box(0);
x_4 = x_534;
goto block_506;
}
}
else
{
lean_object* x_535; 
x_535 = lean_box(0);
x_4 = x_535;
goto block_506;
}
block_506:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eShallowInstantiate), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_EState_fromState___rarg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_TypeClass_Context_slowWhnf___main(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eShallowInstantiate), 2, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = l_EState_fromState___rarg(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_46; lean_object* x_127; lean_object* x_159; uint8_t x_167; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_TypeClass_Context_slowWhnf___main(x_14);
lean_dec(x_14);
lean_inc(x_15);
lean_ctor_set(x_12, 0, x_10);
x_167 = l_Lean_Expr_isMVar(x_9);
if (x_167 == 0)
{
uint8_t x_168; 
x_168 = l_Lean_TypeClass_Context_eIsMeta(x_16);
if (x_168 == 0)
{
x_159 = x_10;
goto block_166;
}
else
{
uint8_t x_169; 
x_169 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_169 == 0)
{
lean_dec(x_15);
x_1 = x_16;
x_2 = x_9;
x_3 = x_12;
goto _start;
}
else
{
x_159 = x_10;
goto block_166;
}
}
}
else
{
uint8_t x_171; 
x_171 = l_Lean_Expr_isMVar(x_16);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_TypeClass_Context_eIsMeta(x_16);
if (x_172 == 0)
{
x_159 = x_10;
goto block_166;
}
else
{
uint8_t x_173; 
x_173 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_173 == 0)
{
lean_dec(x_15);
x_1 = x_16;
x_2 = x_9;
x_3 = x_12;
goto _start;
}
else
{
x_159 = x_10;
goto block_166;
}
}
}
else
{
uint8_t x_175; 
x_175 = lean_expr_eqv(x_9, x_16);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_TypeClass_Context_eIsMeta(x_16);
if (x_176 == 0)
{
x_159 = x_10;
goto block_166;
}
else
{
uint8_t x_177; 
x_177 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_177 == 0)
{
lean_dec(x_15);
x_1 = x_16;
x_2 = x_9;
x_3 = x_12;
goto _start;
}
else
{
x_159 = x_10;
goto block_166;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_12);
lean_dec(x_16);
lean_dec(x_9);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_10);
lean_ctor_set(x_179, 1, x_15);
return x_179;
}
}
}
block_45:
{
uint8_t x_18; 
lean_dec(x_17);
x_18 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_19 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_20 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_expr_dbg_to_string(x_16);
lean_dec(x_16);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
else
{
uint8_t x_27; 
lean_inc(x_9);
lean_inc(x_16);
x_27 = l_Lean_TypeClass_Context_eOccursIn(x_16, x_9);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_15);
x_28 = l_Lean_TypeClass_Context_eMetaIdx(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
x_29 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_30 = lean_unsigned_to_nat(215u);
x_31 = lean_unsigned_to_nat(20u);
x_32 = l_Lean_TypeClass_Context_eUnify___main___closed__2;
x_33 = l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(x_29, x_30, x_31, x_32, x_12);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eAssignIdx___boxed), 3, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_16);
x_36 = l_EState_fromState___rarg(x_35, x_12);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
x_37 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_38 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_expr_dbg_to_string(x_16);
lean_dec(x_16);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
return x_44;
}
}
}
block_126:
{
uint8_t x_47; 
lean_dec(x_46);
x_47 = l_Lean_Expr_isApp(x_9);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isForall(x_9);
if (x_48 == 0)
{
x_17 = x_10;
goto block_45;
}
else
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isForall(x_16);
if (x_49 == 0)
{
x_17 = x_10;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_15);
x_50 = l_Lean_Expr_bindingDomain(x_9);
x_51 = l_Lean_Expr_bindingDomain(x_16);
x_52 = l_Lean_TypeClass_Context_eUnify___main(x_50, x_51, x_12);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_10);
x_55 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_56 = l_Lean_Expr_bindingBody(x_16);
lean_dec(x_16);
x_1 = x_55;
x_2 = x_56;
x_3 = x_52;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_10);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_61 = l_Lean_Expr_bindingBody(x_16);
lean_dec(x_16);
x_1 = x_60;
x_2 = x_61;
x_3 = x_59;
goto _start;
}
}
else
{
uint8_t x_63; 
lean_dec(x_16);
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
else
{
uint8_t x_67; 
x_67 = l_Lean_Expr_isApp(x_16);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_isForall(x_9);
if (x_68 == 0)
{
x_17 = x_10;
goto block_45;
}
else
{
uint8_t x_69; 
x_69 = l_Lean_Expr_isForall(x_16);
if (x_69 == 0)
{
x_17 = x_10;
goto block_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_15);
x_70 = l_Lean_Expr_bindingDomain(x_9);
x_71 = l_Lean_Expr_bindingDomain(x_16);
x_72 = l_Lean_TypeClass_Context_eUnify___main(x_70, x_71, x_12);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_10);
x_75 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_76 = l_Lean_Expr_bindingBody(x_16);
lean_dec(x_16);
x_1 = x_75;
x_2 = x_76;
x_3 = x_72;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_81 = l_Lean_Expr_bindingBody(x_16);
lean_dec(x_16);
x_1 = x_80;
x_2 = x_81;
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_83; 
lean_dec(x_16);
lean_dec(x_9);
x_83 = !lean_is_exclusive(x_72);
if (x_83 == 0)
{
return x_72;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_72, 0);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_72);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_87 = lean_box(0);
x_88 = l_Lean_Expr_getAppArgsAux___main(x_9, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_List_lengthAux___main___rarg(x_88, x_89);
x_91 = l_Lean_Expr_getAppArgsAux___main(x_16, x_87);
x_92 = l_List_lengthAux___main___rarg(x_91, x_89);
x_93 = lean_nat_dec_eq(x_90, x_92);
lean_dec(x_92);
lean_dec(x_90);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_91);
lean_dec(x_88);
x_94 = l_Lean_Expr_isForall(x_9);
if (x_94 == 0)
{
x_17 = x_10;
goto block_45;
}
else
{
uint8_t x_95; 
x_95 = l_Lean_Expr_isForall(x_16);
if (x_95 == 0)
{
x_17 = x_10;
goto block_45;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_15);
x_96 = l_Lean_Expr_bindingDomain(x_9);
x_97 = l_Lean_Expr_bindingDomain(x_16);
x_98 = l_Lean_TypeClass_Context_eUnify___main(x_96, x_97, x_12);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_10);
x_101 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_102 = l_Lean_Expr_bindingBody(x_16);
lean_dec(x_16);
x_1 = x_101;
x_2 = x_102;
x_3 = x_98;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_10);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_107 = l_Lean_Expr_bindingBody(x_16);
lean_dec(x_16);
x_1 = x_106;
x_2 = x_107;
x_3 = x_105;
goto _start;
}
}
else
{
uint8_t x_109; 
lean_dec(x_16);
lean_dec(x_9);
x_109 = !lean_is_exclusive(x_98);
if (x_109 == 0)
{
return x_98;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_98, 0);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_98);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_15);
x_113 = l_Lean_Expr_getAppFn___main(x_9);
lean_dec(x_9);
x_114 = l_Lean_Expr_getAppFn___main(x_16);
lean_dec(x_16);
x_115 = l_Lean_TypeClass_Context_eUnify___main(x_113, x_114, x_12);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_10);
x_118 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(x_88, x_91, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_10);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(x_88, x_91, x_120);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_91);
lean_dec(x_88);
x_122 = !lean_is_exclusive(x_115);
if (x_122 == 0)
{
return x_115;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_115, 0);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_115);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
}
}
block_158:
{
uint8_t x_128; 
lean_dec(x_127);
x_128 = l_Lean_Expr_isFVar(x_9);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = l_Lean_Expr_isConst(x_9);
if (x_129 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
uint8_t x_130; 
x_130 = l_Lean_Expr_isConst(x_16);
if (x_130 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = l_Lean_Expr_constName(x_9);
x_132 = l_Lean_Expr_constName(x_16);
x_133 = lean_name_dec_eq(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_15);
x_134 = l_Lean_Expr_constLevels(x_9);
lean_dec(x_9);
x_135 = l_Lean_Expr_constLevels(x_16);
lean_dec(x_16);
x_136 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_134, x_135, x_12);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
x_137 = l_Lean_Expr_isFVar(x_16);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = l_Lean_Expr_isConst(x_9);
if (x_138 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
uint8_t x_139; 
x_139 = l_Lean_Expr_isConst(x_16);
if (x_139 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Expr_constName(x_9);
x_141 = l_Lean_Expr_constName(x_16);
x_142 = lean_name_dec_eq(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (x_142 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_15);
x_143 = l_Lean_Expr_constLevels(x_9);
lean_dec(x_9);
x_144 = l_Lean_Expr_constLevels(x_16);
lean_dec(x_16);
x_145 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_143, x_144, x_12);
return x_145;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = l_Lean_Expr_fvarName(x_9);
x_147 = l_Lean_Expr_fvarName(x_16);
x_148 = lean_name_dec_eq(x_146, x_147);
lean_dec(x_147);
lean_dec(x_146);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Expr_isConst(x_9);
if (x_149 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
uint8_t x_150; 
x_150 = l_Lean_Expr_isConst(x_16);
if (x_150 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = l_Lean_Expr_constName(x_9);
x_152 = l_Lean_Expr_constName(x_16);
x_153 = lean_name_dec_eq(x_151, x_152);
lean_dec(x_152);
lean_dec(x_151);
if (x_153 == 0)
{
x_46 = x_10;
goto block_126;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_15);
x_154 = l_Lean_Expr_constLevels(x_9);
lean_dec(x_9);
x_155 = l_Lean_Expr_constLevels(x_16);
lean_dec(x_16);
x_156 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_154, x_155, x_12);
return x_156;
}
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_12);
lean_dec(x_16);
lean_dec(x_9);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_10);
lean_ctor_set(x_157, 1, x_15);
return x_157;
}
}
}
}
block_166:
{
uint8_t x_160; 
lean_dec(x_159);
x_160 = l_Lean_Expr_isBVar(x_9);
if (x_160 == 0)
{
x_127 = x_10;
goto block_158;
}
else
{
uint8_t x_161; 
x_161 = l_Lean_Expr_isBVar(x_16);
if (x_161 == 0)
{
x_127 = x_10;
goto block_158;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = l_Lean_Expr_bvarIdx(x_9);
x_163 = l_Lean_Expr_bvarIdx(x_16);
x_164 = lean_nat_dec_eq(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
x_127 = x_10;
goto block_158;
}
else
{
lean_object* x_165; 
lean_dec(x_12);
lean_dec(x_16);
lean_dec(x_9);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_10);
lean_ctor_set(x_165, 1, x_15);
return x_165;
}
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_213; lean_object* x_280; lean_object* x_312; uint8_t x_320; 
x_180 = lean_ctor_get(x_12, 0);
x_181 = lean_ctor_get(x_12, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_12);
x_182 = l_Lean_TypeClass_Context_slowWhnf___main(x_180);
lean_dec(x_180);
lean_inc(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_10);
lean_ctor_set(x_183, 1, x_181);
x_320 = l_Lean_Expr_isMVar(x_9);
if (x_320 == 0)
{
uint8_t x_321; 
x_321 = l_Lean_TypeClass_Context_eIsMeta(x_182);
if (x_321 == 0)
{
x_312 = x_10;
goto block_319;
}
else
{
uint8_t x_322; 
x_322 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_322 == 0)
{
lean_dec(x_181);
x_1 = x_182;
x_2 = x_9;
x_3 = x_183;
goto _start;
}
else
{
x_312 = x_10;
goto block_319;
}
}
}
else
{
uint8_t x_324; 
x_324 = l_Lean_Expr_isMVar(x_182);
if (x_324 == 0)
{
uint8_t x_325; 
x_325 = l_Lean_TypeClass_Context_eIsMeta(x_182);
if (x_325 == 0)
{
x_312 = x_10;
goto block_319;
}
else
{
uint8_t x_326; 
x_326 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_326 == 0)
{
lean_dec(x_181);
x_1 = x_182;
x_2 = x_9;
x_3 = x_183;
goto _start;
}
else
{
x_312 = x_10;
goto block_319;
}
}
}
else
{
uint8_t x_328; 
x_328 = lean_expr_eqv(x_9, x_182);
if (x_328 == 0)
{
uint8_t x_329; 
x_329 = l_Lean_TypeClass_Context_eIsMeta(x_182);
if (x_329 == 0)
{
x_312 = x_10;
goto block_319;
}
else
{
uint8_t x_330; 
x_330 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_330 == 0)
{
lean_dec(x_181);
x_1 = x_182;
x_2 = x_9;
x_3 = x_183;
goto _start;
}
else
{
x_312 = x_10;
goto block_319;
}
}
}
else
{
lean_object* x_332; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_9);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_10);
lean_ctor_set(x_332, 1, x_181);
return x_332;
}
}
}
block_212:
{
uint8_t x_185; 
lean_dec(x_184);
x_185 = l_Lean_TypeClass_Context_eIsMeta(x_9);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_183);
x_186 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_187 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_188 = lean_string_append(x_187, x_186);
lean_dec(x_186);
x_189 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_190 = lean_string_append(x_188, x_189);
x_191 = lean_expr_dbg_to_string(x_182);
lean_dec(x_182);
x_192 = lean_string_append(x_190, x_191);
lean_dec(x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_181);
return x_193;
}
else
{
uint8_t x_194; 
lean_inc(x_9);
lean_inc(x_182);
x_194 = l_Lean_TypeClass_Context_eOccursIn(x_182, x_9);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_181);
x_195 = l_Lean_TypeClass_Context_eMetaIdx(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_182);
x_196 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_197 = lean_unsigned_to_nat(215u);
x_198 = lean_unsigned_to_nat(20u);
x_199 = l_Lean_TypeClass_Context_eUnify___main___closed__2;
x_200 = l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(x_196, x_197, x_198, x_199, x_183);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_195, 0);
lean_inc(x_201);
lean_dec(x_195);
x_202 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eAssignIdx___boxed), 3, 2);
lean_closure_set(x_202, 0, x_201);
lean_closure_set(x_202, 1, x_182);
x_203 = l_EState_fromState___rarg(x_202, x_183);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_183);
x_204 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_205 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_206 = lean_string_append(x_205, x_204);
lean_dec(x_204);
x_207 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_208 = lean_string_append(x_206, x_207);
x_209 = lean_expr_dbg_to_string(x_182);
lean_dec(x_182);
x_210 = lean_string_append(x_208, x_209);
lean_dec(x_209);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_181);
return x_211;
}
}
}
block_279:
{
uint8_t x_214; 
lean_dec(x_213);
x_214 = l_Lean_Expr_isApp(x_9);
if (x_214 == 0)
{
uint8_t x_215; 
x_215 = l_Lean_Expr_isForall(x_9);
if (x_215 == 0)
{
x_184 = x_10;
goto block_212;
}
else
{
uint8_t x_216; 
x_216 = l_Lean_Expr_isForall(x_182);
if (x_216 == 0)
{
x_184 = x_10;
goto block_212;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_181);
x_217 = l_Lean_Expr_bindingDomain(x_9);
x_218 = l_Lean_Expr_bindingDomain(x_182);
x_219 = l_Lean_TypeClass_Context_eUnify___main(x_217, x_218, x_183);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_10);
lean_ctor_set(x_222, 1, x_220);
x_223 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_224 = l_Lean_Expr_bindingBody(x_182);
lean_dec(x_182);
x_1 = x_223;
x_2 = x_224;
x_3 = x_222;
goto _start;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_182);
lean_dec(x_9);
x_226 = lean_ctor_get(x_219, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_219, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_228 = x_219;
} else {
 lean_dec_ref(x_219);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
}
else
{
uint8_t x_230; 
x_230 = l_Lean_Expr_isApp(x_182);
if (x_230 == 0)
{
uint8_t x_231; 
x_231 = l_Lean_Expr_isForall(x_9);
if (x_231 == 0)
{
x_184 = x_10;
goto block_212;
}
else
{
uint8_t x_232; 
x_232 = l_Lean_Expr_isForall(x_182);
if (x_232 == 0)
{
x_184 = x_10;
goto block_212;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_181);
x_233 = l_Lean_Expr_bindingDomain(x_9);
x_234 = l_Lean_Expr_bindingDomain(x_182);
x_235 = l_Lean_TypeClass_Context_eUnify___main(x_233, x_234, x_183);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_10);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_240 = l_Lean_Expr_bindingBody(x_182);
lean_dec(x_182);
x_1 = x_239;
x_2 = x_240;
x_3 = x_238;
goto _start;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_182);
lean_dec(x_9);
x_242 = lean_ctor_get(x_235, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_235, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_244 = x_235;
} else {
 lean_dec_ref(x_235);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_246 = lean_box(0);
x_247 = l_Lean_Expr_getAppArgsAux___main(x_9, x_246);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_List_lengthAux___main___rarg(x_247, x_248);
x_250 = l_Lean_Expr_getAppArgsAux___main(x_182, x_246);
x_251 = l_List_lengthAux___main___rarg(x_250, x_248);
x_252 = lean_nat_dec_eq(x_249, x_251);
lean_dec(x_251);
lean_dec(x_249);
if (x_252 == 0)
{
uint8_t x_253; 
lean_dec(x_250);
lean_dec(x_247);
x_253 = l_Lean_Expr_isForall(x_9);
if (x_253 == 0)
{
x_184 = x_10;
goto block_212;
}
else
{
uint8_t x_254; 
x_254 = l_Lean_Expr_isForall(x_182);
if (x_254 == 0)
{
x_184 = x_10;
goto block_212;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_181);
x_255 = l_Lean_Expr_bindingDomain(x_9);
x_256 = l_Lean_Expr_bindingDomain(x_182);
x_257 = l_Lean_TypeClass_Context_eUnify___main(x_255, x_256, x_183);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_10);
lean_ctor_set(x_260, 1, x_258);
x_261 = l_Lean_Expr_bindingBody(x_9);
lean_dec(x_9);
x_262 = l_Lean_Expr_bindingBody(x_182);
lean_dec(x_182);
x_1 = x_261;
x_2 = x_262;
x_3 = x_260;
goto _start;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_182);
lean_dec(x_9);
x_264 = lean_ctor_get(x_257, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_257, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_266 = x_257;
} else {
 lean_dec_ref(x_257);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_181);
x_268 = l_Lean_Expr_getAppFn___main(x_9);
lean_dec(x_9);
x_269 = l_Lean_Expr_getAppFn___main(x_182);
lean_dec(x_182);
x_270 = l_Lean_TypeClass_Context_eUnify___main(x_268, x_269, x_183);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_10);
lean_ctor_set(x_273, 1, x_271);
x_274 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(x_247, x_250, x_273);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_250);
lean_dec(x_247);
x_275 = lean_ctor_get(x_270, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_270, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_277 = x_270;
} else {
 lean_dec_ref(x_270);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
}
}
block_311:
{
uint8_t x_281; 
lean_dec(x_280);
x_281 = l_Lean_Expr_isFVar(x_9);
if (x_281 == 0)
{
uint8_t x_282; 
x_282 = l_Lean_Expr_isConst(x_9);
if (x_282 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
uint8_t x_283; 
x_283 = l_Lean_Expr_isConst(x_182);
if (x_283 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = l_Lean_Expr_constName(x_9);
x_285 = l_Lean_Expr_constName(x_182);
x_286 = lean_name_dec_eq(x_284, x_285);
lean_dec(x_285);
lean_dec(x_284);
if (x_286 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_181);
x_287 = l_Lean_Expr_constLevels(x_9);
lean_dec(x_9);
x_288 = l_Lean_Expr_constLevels(x_182);
lean_dec(x_182);
x_289 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_287, x_288, x_183);
return x_289;
}
}
}
}
else
{
uint8_t x_290; 
x_290 = l_Lean_Expr_isFVar(x_182);
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = l_Lean_Expr_isConst(x_9);
if (x_291 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
uint8_t x_292; 
x_292 = l_Lean_Expr_isConst(x_182);
if (x_292 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = l_Lean_Expr_constName(x_9);
x_294 = l_Lean_Expr_constName(x_182);
x_295 = lean_name_dec_eq(x_293, x_294);
lean_dec(x_294);
lean_dec(x_293);
if (x_295 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_181);
x_296 = l_Lean_Expr_constLevels(x_9);
lean_dec(x_9);
x_297 = l_Lean_Expr_constLevels(x_182);
lean_dec(x_182);
x_298 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_296, x_297, x_183);
return x_298;
}
}
}
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = l_Lean_Expr_fvarName(x_9);
x_300 = l_Lean_Expr_fvarName(x_182);
x_301 = lean_name_dec_eq(x_299, x_300);
lean_dec(x_300);
lean_dec(x_299);
if (x_301 == 0)
{
uint8_t x_302; 
x_302 = l_Lean_Expr_isConst(x_9);
if (x_302 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
uint8_t x_303; 
x_303 = l_Lean_Expr_isConst(x_182);
if (x_303 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = l_Lean_Expr_constName(x_9);
x_305 = l_Lean_Expr_constName(x_182);
x_306 = lean_name_dec_eq(x_304, x_305);
lean_dec(x_305);
lean_dec(x_304);
if (x_306 == 0)
{
x_213 = x_10;
goto block_279;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_181);
x_307 = l_Lean_Expr_constLevels(x_9);
lean_dec(x_9);
x_308 = l_Lean_Expr_constLevels(x_182);
lean_dec(x_182);
x_309 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_307, x_308, x_183);
return x_309;
}
}
}
}
else
{
lean_object* x_310; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_9);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_10);
lean_ctor_set(x_310, 1, x_181);
return x_310;
}
}
}
}
block_319:
{
uint8_t x_313; 
lean_dec(x_312);
x_313 = l_Lean_Expr_isBVar(x_9);
if (x_313 == 0)
{
x_280 = x_10;
goto block_311;
}
else
{
uint8_t x_314; 
x_314 = l_Lean_Expr_isBVar(x_182);
if (x_314 == 0)
{
x_280 = x_10;
goto block_311;
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_315 = l_Lean_Expr_bvarIdx(x_9);
x_316 = l_Lean_Expr_bvarIdx(x_182);
x_317 = lean_nat_dec_eq(x_315, x_316);
lean_dec(x_316);
lean_dec(x_315);
if (x_317 == 0)
{
x_280 = x_10;
goto block_311;
}
else
{
lean_object* x_318; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_9);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_10);
lean_ctor_set(x_318, 1, x_181);
return x_318;
}
}
}
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_9);
x_333 = !lean_is_exclusive(x_12);
if (x_333 == 0)
{
return x_12;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_12, 0);
x_335 = lean_ctor_get(x_12, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_12);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_6, 0);
x_338 = lean_ctor_get(x_6, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_6);
x_339 = l_Lean_TypeClass_Context_slowWhnf___main(x_337);
lean_dec(x_337);
x_340 = lean_box(0);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_338);
x_342 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eShallowInstantiate), 2, 1);
lean_closure_set(x_342, 0, x_2);
x_343 = l_EState_fromState___rarg(x_342, x_341);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_378; lean_object* x_445; lean_object* x_477; uint8_t x_485; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
x_347 = l_Lean_TypeClass_Context_slowWhnf___main(x_344);
lean_dec(x_344);
lean_inc(x_345);
if (lean_is_scalar(x_346)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_346;
}
lean_ctor_set(x_348, 0, x_340);
lean_ctor_set(x_348, 1, x_345);
x_485 = l_Lean_Expr_isMVar(x_339);
if (x_485 == 0)
{
uint8_t x_486; 
x_486 = l_Lean_TypeClass_Context_eIsMeta(x_347);
if (x_486 == 0)
{
x_477 = x_340;
goto block_484;
}
else
{
uint8_t x_487; 
x_487 = l_Lean_TypeClass_Context_eIsMeta(x_339);
if (x_487 == 0)
{
lean_dec(x_345);
x_1 = x_347;
x_2 = x_339;
x_3 = x_348;
goto _start;
}
else
{
x_477 = x_340;
goto block_484;
}
}
}
else
{
uint8_t x_489; 
x_489 = l_Lean_Expr_isMVar(x_347);
if (x_489 == 0)
{
uint8_t x_490; 
x_490 = l_Lean_TypeClass_Context_eIsMeta(x_347);
if (x_490 == 0)
{
x_477 = x_340;
goto block_484;
}
else
{
uint8_t x_491; 
x_491 = l_Lean_TypeClass_Context_eIsMeta(x_339);
if (x_491 == 0)
{
lean_dec(x_345);
x_1 = x_347;
x_2 = x_339;
x_3 = x_348;
goto _start;
}
else
{
x_477 = x_340;
goto block_484;
}
}
}
else
{
uint8_t x_493; 
x_493 = lean_expr_eqv(x_339, x_347);
if (x_493 == 0)
{
uint8_t x_494; 
x_494 = l_Lean_TypeClass_Context_eIsMeta(x_347);
if (x_494 == 0)
{
x_477 = x_340;
goto block_484;
}
else
{
uint8_t x_495; 
x_495 = l_Lean_TypeClass_Context_eIsMeta(x_339);
if (x_495 == 0)
{
lean_dec(x_345);
x_1 = x_347;
x_2 = x_339;
x_3 = x_348;
goto _start;
}
else
{
x_477 = x_340;
goto block_484;
}
}
}
else
{
lean_object* x_497; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_339);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_340);
lean_ctor_set(x_497, 1, x_345);
return x_497;
}
}
}
block_377:
{
uint8_t x_350; 
lean_dec(x_349);
x_350 = l_Lean_TypeClass_Context_eIsMeta(x_339);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_348);
x_351 = lean_expr_dbg_to_string(x_339);
lean_dec(x_339);
x_352 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_353 = lean_string_append(x_352, x_351);
lean_dec(x_351);
x_354 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_355 = lean_string_append(x_353, x_354);
x_356 = lean_expr_dbg_to_string(x_347);
lean_dec(x_347);
x_357 = lean_string_append(x_355, x_356);
lean_dec(x_356);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_345);
return x_358;
}
else
{
uint8_t x_359; 
lean_inc(x_339);
lean_inc(x_347);
x_359 = l_Lean_TypeClass_Context_eOccursIn(x_347, x_339);
if (x_359 == 0)
{
lean_object* x_360; 
lean_dec(x_345);
x_360 = l_Lean_TypeClass_Context_eMetaIdx(x_339);
lean_dec(x_339);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_347);
x_361 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_362 = lean_unsigned_to_nat(215u);
x_363 = lean_unsigned_to_nat(20u);
x_364 = l_Lean_TypeClass_Context_eUnify___main___closed__2;
x_365 = l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(x_361, x_362, x_363, x_364, x_348);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_360, 0);
lean_inc(x_366);
lean_dec(x_360);
x_367 = lean_alloc_closure((void*)(l_Lean_TypeClass_Context_eAssignIdx___boxed), 3, 2);
lean_closure_set(x_367, 0, x_366);
lean_closure_set(x_367, 1, x_347);
x_368 = l_EState_fromState___rarg(x_367, x_348);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_348);
x_369 = lean_expr_dbg_to_string(x_339);
lean_dec(x_339);
x_370 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_371 = lean_string_append(x_370, x_369);
lean_dec(x_369);
x_372 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_373 = lean_string_append(x_371, x_372);
x_374 = lean_expr_dbg_to_string(x_347);
lean_dec(x_347);
x_375 = lean_string_append(x_373, x_374);
lean_dec(x_374);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_345);
return x_376;
}
}
}
block_444:
{
uint8_t x_379; 
lean_dec(x_378);
x_379 = l_Lean_Expr_isApp(x_339);
if (x_379 == 0)
{
uint8_t x_380; 
x_380 = l_Lean_Expr_isForall(x_339);
if (x_380 == 0)
{
x_349 = x_340;
goto block_377;
}
else
{
uint8_t x_381; 
x_381 = l_Lean_Expr_isForall(x_347);
if (x_381 == 0)
{
x_349 = x_340;
goto block_377;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_345);
x_382 = l_Lean_Expr_bindingDomain(x_339);
x_383 = l_Lean_Expr_bindingDomain(x_347);
x_384 = l_Lean_TypeClass_Context_eUnify___main(x_382, x_383, x_348);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_386 = x_384;
} else {
 lean_dec_ref(x_384);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_340);
lean_ctor_set(x_387, 1, x_385);
x_388 = l_Lean_Expr_bindingBody(x_339);
lean_dec(x_339);
x_389 = l_Lean_Expr_bindingBody(x_347);
lean_dec(x_347);
x_1 = x_388;
x_2 = x_389;
x_3 = x_387;
goto _start;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_347);
lean_dec(x_339);
x_391 = lean_ctor_get(x_384, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_384, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_393 = x_384;
} else {
 lean_dec_ref(x_384);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
}
}
else
{
uint8_t x_395; 
x_395 = l_Lean_Expr_isApp(x_347);
if (x_395 == 0)
{
uint8_t x_396; 
x_396 = l_Lean_Expr_isForall(x_339);
if (x_396 == 0)
{
x_349 = x_340;
goto block_377;
}
else
{
uint8_t x_397; 
x_397 = l_Lean_Expr_isForall(x_347);
if (x_397 == 0)
{
x_349 = x_340;
goto block_377;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_345);
x_398 = l_Lean_Expr_bindingDomain(x_339);
x_399 = l_Lean_Expr_bindingDomain(x_347);
x_400 = l_Lean_TypeClass_Context_eUnify___main(x_398, x_399, x_348);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_402 = x_400;
} else {
 lean_dec_ref(x_400);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_340);
lean_ctor_set(x_403, 1, x_401);
x_404 = l_Lean_Expr_bindingBody(x_339);
lean_dec(x_339);
x_405 = l_Lean_Expr_bindingBody(x_347);
lean_dec(x_347);
x_1 = x_404;
x_2 = x_405;
x_3 = x_403;
goto _start;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_347);
lean_dec(x_339);
x_407 = lean_ctor_get(x_400, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_400, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_409 = x_400;
} else {
 lean_dec_ref(x_400);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_411 = lean_box(0);
x_412 = l_Lean_Expr_getAppArgsAux___main(x_339, x_411);
x_413 = lean_unsigned_to_nat(0u);
x_414 = l_List_lengthAux___main___rarg(x_412, x_413);
x_415 = l_Lean_Expr_getAppArgsAux___main(x_347, x_411);
x_416 = l_List_lengthAux___main___rarg(x_415, x_413);
x_417 = lean_nat_dec_eq(x_414, x_416);
lean_dec(x_416);
lean_dec(x_414);
if (x_417 == 0)
{
uint8_t x_418; 
lean_dec(x_415);
lean_dec(x_412);
x_418 = l_Lean_Expr_isForall(x_339);
if (x_418 == 0)
{
x_349 = x_340;
goto block_377;
}
else
{
uint8_t x_419; 
x_419 = l_Lean_Expr_isForall(x_347);
if (x_419 == 0)
{
x_349 = x_340;
goto block_377;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_345);
x_420 = l_Lean_Expr_bindingDomain(x_339);
x_421 = l_Lean_Expr_bindingDomain(x_347);
x_422 = l_Lean_TypeClass_Context_eUnify___main(x_420, x_421, x_348);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_424 = x_422;
} else {
 lean_dec_ref(x_422);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_340);
lean_ctor_set(x_425, 1, x_423);
x_426 = l_Lean_Expr_bindingBody(x_339);
lean_dec(x_339);
x_427 = l_Lean_Expr_bindingBody(x_347);
lean_dec(x_347);
x_1 = x_426;
x_2 = x_427;
x_3 = x_425;
goto _start;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_347);
lean_dec(x_339);
x_429 = lean_ctor_get(x_422, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_422, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_431 = x_422;
} else {
 lean_dec_ref(x_422);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_345);
x_433 = l_Lean_Expr_getAppFn___main(x_339);
lean_dec(x_339);
x_434 = l_Lean_Expr_getAppFn___main(x_347);
lean_dec(x_347);
x_435 = l_Lean_TypeClass_Context_eUnify___main(x_433, x_434, x_348);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_437 = x_435;
} else {
 lean_dec_ref(x_435);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_340);
lean_ctor_set(x_438, 1, x_436);
x_439 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(x_412, x_415, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_415);
lean_dec(x_412);
x_440 = lean_ctor_get(x_435, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_435, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_442 = x_435;
} else {
 lean_dec_ref(x_435);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
}
}
block_476:
{
uint8_t x_446; 
lean_dec(x_445);
x_446 = l_Lean_Expr_isFVar(x_339);
if (x_446 == 0)
{
uint8_t x_447; 
x_447 = l_Lean_Expr_isConst(x_339);
if (x_447 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
uint8_t x_448; 
x_448 = l_Lean_Expr_isConst(x_347);
if (x_448 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_449 = l_Lean_Expr_constName(x_339);
x_450 = l_Lean_Expr_constName(x_347);
x_451 = lean_name_dec_eq(x_449, x_450);
lean_dec(x_450);
lean_dec(x_449);
if (x_451 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_345);
x_452 = l_Lean_Expr_constLevels(x_339);
lean_dec(x_339);
x_453 = l_Lean_Expr_constLevels(x_347);
lean_dec(x_347);
x_454 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_452, x_453, x_348);
return x_454;
}
}
}
}
else
{
uint8_t x_455; 
x_455 = l_Lean_Expr_isFVar(x_347);
if (x_455 == 0)
{
uint8_t x_456; 
x_456 = l_Lean_Expr_isConst(x_339);
if (x_456 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
uint8_t x_457; 
x_457 = l_Lean_Expr_isConst(x_347);
if (x_457 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_458 = l_Lean_Expr_constName(x_339);
x_459 = l_Lean_Expr_constName(x_347);
x_460 = lean_name_dec_eq(x_458, x_459);
lean_dec(x_459);
lean_dec(x_458);
if (x_460 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_345);
x_461 = l_Lean_Expr_constLevels(x_339);
lean_dec(x_339);
x_462 = l_Lean_Expr_constLevels(x_347);
lean_dec(x_347);
x_463 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_461, x_462, x_348);
return x_463;
}
}
}
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_464 = l_Lean_Expr_fvarName(x_339);
x_465 = l_Lean_Expr_fvarName(x_347);
x_466 = lean_name_dec_eq(x_464, x_465);
lean_dec(x_465);
lean_dec(x_464);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = l_Lean_Expr_isConst(x_339);
if (x_467 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
uint8_t x_468; 
x_468 = l_Lean_Expr_isConst(x_347);
if (x_468 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_469 = l_Lean_Expr_constName(x_339);
x_470 = l_Lean_Expr_constName(x_347);
x_471 = lean_name_dec_eq(x_469, x_470);
lean_dec(x_470);
lean_dec(x_469);
if (x_471 == 0)
{
x_378 = x_340;
goto block_444;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_345);
x_472 = l_Lean_Expr_constLevels(x_339);
lean_dec(x_339);
x_473 = l_Lean_Expr_constLevels(x_347);
lean_dec(x_347);
x_474 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_472, x_473, x_348);
return x_474;
}
}
}
}
else
{
lean_object* x_475; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_339);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_340);
lean_ctor_set(x_475, 1, x_345);
return x_475;
}
}
}
}
block_484:
{
uint8_t x_478; 
lean_dec(x_477);
x_478 = l_Lean_Expr_isBVar(x_339);
if (x_478 == 0)
{
x_445 = x_340;
goto block_476;
}
else
{
uint8_t x_479; 
x_479 = l_Lean_Expr_isBVar(x_347);
if (x_479 == 0)
{
x_445 = x_340;
goto block_476;
}
else
{
lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_480 = l_Lean_Expr_bvarIdx(x_339);
x_481 = l_Lean_Expr_bvarIdx(x_347);
x_482 = lean_nat_dec_eq(x_480, x_481);
lean_dec(x_481);
lean_dec(x_480);
if (x_482 == 0)
{
x_445 = x_340;
goto block_476;
}
else
{
lean_object* x_483; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_339);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_340);
lean_ctor_set(x_483, 1, x_345);
return x_483;
}
}
}
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_339);
x_498 = lean_ctor_get(x_343, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_343, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_500 = x_343;
} else {
 lean_dec_ref(x_343);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_499);
return x_501;
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_2);
x_502 = !lean_is_exclusive(x_6);
if (x_502 == 0)
{
return x_6;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_6, 0);
x_504 = lean_ctor_get(x_6, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_6);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_TypeClass_Context_eUnify(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_TypeClass_Context_eInstantiate___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_5);
lean_dec(x_5);
x_8 = l_List_map___main___at_Lean_TypeClass_Context_eInstantiate___main___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_TypeClass_Context_uInstantiate___main(x_1, x_9);
lean_dec(x_9);
x_12 = l_List_map___main___at_Lean_TypeClass_Context_eInstantiate___main___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_eInstantiate___main(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_has_mvar(x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_map___main___at_Lean_TypeClass_Context_eInstantiate___main___spec__1(x_1, x_5);
x_7 = lean_expr_mk_const(x_4, x_6);
return x_7;
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_10 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_8);
x_11 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_9);
x_12 = lean_expr_mk_app(x_10, x_11);
return x_12;
}
case 6:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
x_17 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_15);
x_18 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_16);
x_19 = lean_expr_mk_lambda(x_13, x_14, x_17, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_22);
x_25 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_23);
x_26 = lean_expr_mk_pi(x_20, x_21, x_24, x_25);
return x_26;
}
default: 
{
lean_object* x_27; 
x_27 = l_Lean_TypeClass_Context_eMetaIdx(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_1);
x_29 = l_Lean_TypeClass_Context_eLookupIdx(x_28, x_1);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_2 = x_31;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_TypeClass_Context_eInstantiate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eInstantiate___main(x_1, x_2);
return x_3;
}
}
lean_object* l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_9, x_2);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
else
{
lean_object* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = lean_nat_dec_lt(x_2, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_17, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_19, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_16, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_nat_dec_lt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_29, x_2);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_31, x_2, x_3);
lean_ctor_set(x_1, 3, x_35);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_31, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = 0;
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
x_60 = 1;
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_60);
lean_ctor_set(x_36, 3, x_59);
lean_ctor_set(x_36, 2, x_58);
lean_ctor_set(x_36, 1, x_57);
lean_ctor_set(x_36, 0, x_56);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_60);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
lean_ctor_set(x_36, 3, x_64);
lean_ctor_set(x_36, 2, x_63);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_61);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_65);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = 1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 4, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_28);
lean_ctor_set(x_75, 1, x_29);
lean_ctor_set(x_75, 2, x_30);
lean_ctor_set(x_75, 3, x_37);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_36, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_36, 0);
lean_dec(x_79);
x_80 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_36, 1);
x_82 = lean_ctor_get(x_36, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_38);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
x_91 = lean_ctor_get(x_37, 2);
x_92 = lean_ctor_get(x_37, 3);
x_93 = 1;
lean_ctor_set(x_37, 3, x_89);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_93);
lean_ctor_set(x_36, 0, x_92);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
x_96 = lean_ctor_get(x_37, 2);
x_97 = lean_ctor_get(x_37, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
x_98 = 1;
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_29);
lean_ctor_set(x_99, 2, x_30);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_98);
lean_ctor_set(x_36, 0, x_97);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_98);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_96);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_36, 1);
x_101 = lean_ctor_get(x_36, 2);
x_102 = lean_ctor_get(x_36, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_103 = lean_ctor_get(x_37, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_107 = x_37;
} else {
 lean_dec_ref(x_37);
 x_107 = lean_box(0);
}
x_108 = 1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_28);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_30);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_110);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_36, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_36, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_36, 0);
lean_dec(x_114);
x_115 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_36, 1);
x_117 = lean_ctor_get(x_36, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = 0;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_1);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_36, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_111);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
x_127 = lean_ctor_get(x_111, 2);
x_128 = lean_ctor_get(x_111, 3);
lean_inc(x_37);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set(x_111, 2, x_30);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_28);
x_129 = !lean_is_exclusive(x_37);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_37, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_37, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_37, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
lean_ctor_set(x_37, 3, x_128);
lean_ctor_set(x_37, 2, x_127);
lean_ctor_set(x_37, 1, x_126);
lean_ctor_set(x_37, 0, x_125);
lean_ctor_set(x_36, 3, x_37);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
lean_object* x_134; 
lean_dec(x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_134);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_111, 0);
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_111);
lean_inc(x_37);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_140 = x_37;
} else {
 lean_dec_ref(x_37);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_141);
lean_ctor_set(x_36, 0, x_139);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_36, 1);
x_143 = lean_ctor_get(x_36, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_ctor_get(x_111, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_111, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_111, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_111, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_148 = x_111;
} else {
 lean_dec_ref(x_111);
 x_148 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_29);
lean_ctor_set(x_149, 2, x_30);
lean_ctor_set(x_149, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_150 = x_37;
} else {
 lean_dec_ref(x_37);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_142);
lean_ctor_set(x_152, 2, x_143);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_36);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_36, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_36, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_37, 0);
x_159 = lean_ctor_get(x_37, 1);
x_160 = lean_ctor_get(x_37, 2);
x_161 = lean_ctor_get(x_37, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_37);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean_ctor_set(x_36, 0, x_162);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_163);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_36, 1);
x_165 = lean_ctor_get(x_36, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_36);
x_166 = lean_ctor_get(x_37, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_37, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_37, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_37, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_170 = x_37;
} else {
 lean_dec_ref(x_37);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8_t x_174; 
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_28, x_2, x_3);
lean_ctor_set(x_1, 0, x_175);
return x_1;
}
else
{
lean_object* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_28, x_2, x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_free_object(x_1);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 3);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_176, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_176, 0);
lean_dec(x_181);
x_182 = 0;
lean_ctor_set(x_176, 0, x_178);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_176, 1);
x_185 = lean_ctor_get(x_176, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = 0;
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8_t x_189; 
x_189 = lean_ctor_get_uint8(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_176, 1);
x_192 = lean_ctor_get(x_176, 2);
x_193 = lean_ctor_get(x_176, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_176, 0);
lean_dec(x_194);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 2);
x_199 = lean_ctor_get(x_178, 3);
x_200 = 1;
lean_ctor_set(x_178, 3, x_196);
lean_ctor_set(x_178, 2, x_192);
lean_ctor_set(x_178, 1, x_191);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_200);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_199);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_200);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_198);
lean_ctor_set(x_1, 1, x_197);
lean_ctor_set(x_1, 0, x_178);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_178, 0);
x_202 = lean_ctor_get(x_178, 1);
x_203 = lean_ctor_get(x_178, 2);
x_204 = lean_ctor_get(x_178, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_178);
x_205 = 1;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_177);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_204);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_205);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_203);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_176, 1);
x_208 = lean_ctor_get(x_176, 2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_176);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_178, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_178, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 x_213 = x_178;
} else {
 lean_dec_ref(x_178);
 x_213 = lean_box(0);
}
x_214 = 1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_177);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_208);
lean_ctor_set(x_215, 3, x_209);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_29);
lean_ctor_set(x_216, 2, x_30);
lean_ctor_set(x_216, 3, x_31);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_214);
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_176);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 0);
lean_dec(x_219);
x_220 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_220);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_176, 1);
x_222 = lean_ctor_get(x_176, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_177);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_176, 1);
x_228 = lean_ctor_get(x_176, 2);
x_229 = lean_ctor_get(x_176, 3);
x_230 = lean_ctor_get(x_176, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_177);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = 1;
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_232);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_177);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_177, 0);
x_234 = lean_ctor_get(x_177, 1);
x_235 = lean_ctor_get(x_177, 2);
x_236 = lean_ctor_get(x_177, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_177);
x_237 = 1;
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_237);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_237);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_176, 1);
x_240 = lean_ctor_get(x_176, 2);
x_241 = lean_ctor_get(x_176, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_242 = lean_ctor_get(x_177, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_177, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_177, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_177, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_246 = x_177;
} else {
 lean_dec_ref(x_177);
 x_246 = lean_box(0);
}
x_247 = 1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
lean_ctor_set(x_248, 2, x_244);
lean_ctor_set(x_248, 3, x_245);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_29);
lean_ctor_set(x_249, 2, x_30);
lean_ctor_set(x_249, 3, x_31);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_249);
lean_ctor_set(x_1, 2, x_240);
lean_ctor_set(x_1, 1, x_239);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_176, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_176, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_176, 0);
lean_dec(x_253);
x_254 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_254);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_176, 1);
x_256 = lean_ctor_get(x_176, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_176);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_177);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8_t x_260; 
lean_free_object(x_1);
x_260 = !lean_is_exclusive(x_176);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_261 = lean_ctor_get(x_176, 1);
x_262 = lean_ctor_get(x_176, 2);
x_263 = lean_ctor_get(x_176, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_176, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
x_268 = lean_ctor_get(x_250, 2);
x_269 = lean_ctor_get(x_250, 3);
lean_inc(x_177);
lean_ctor_set(x_250, 3, x_266);
lean_ctor_set(x_250, 2, x_262);
lean_ctor_set(x_250, 1, x_261);
lean_ctor_set(x_250, 0, x_177);
x_270 = !lean_is_exclusive(x_177);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_177, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_177, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_177, 0);
lean_dec(x_274);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
lean_ctor_set(x_177, 3, x_31);
lean_ctor_set(x_177, 2, x_30);
lean_ctor_set(x_177, 1, x_29);
lean_ctor_set(x_177, 0, x_269);
lean_ctor_set(x_176, 3, x_177);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
lean_object* x_275; 
lean_dec(x_177);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_29);
lean_ctor_set(x_275, 2, x_30);
lean_ctor_set(x_275, 3, x_31);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_275);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
x_278 = lean_ctor_get(x_250, 2);
x_279 = lean_ctor_get(x_250, 3);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
lean_inc(x_177);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_177);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_262);
lean_ctor_set(x_280, 3, x_276);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_281 = x_177;
} else {
 lean_dec_ref(x_177);
 x_281 = lean_box(0);
}
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 4, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_29);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_31);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_282);
lean_ctor_set(x_176, 2, x_278);
lean_ctor_set(x_176, 1, x_277);
lean_ctor_set(x_176, 0, x_280);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_176, 1);
x_284 = lean_ctor_get(x_176, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_176);
x_285 = lean_ctor_get(x_250, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_250, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
lean_inc(x_177);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_177);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_285);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_291 = x_177;
} else {
 lean_dec_ref(x_177);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_29);
lean_ctor_set(x_292, 2, x_30);
lean_ctor_set(x_292, 3, x_31);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_176);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_176, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_176, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_177);
if (x_297 == 0)
{
uint8_t x_298; 
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_177, 0);
x_300 = lean_ctor_get(x_177, 1);
x_301 = lean_ctor_get(x_177, 2);
x_302 = lean_ctor_get(x_177, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_177);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean_ctor_set(x_176, 0, x_303);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_304);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_305 = lean_ctor_get(x_176, 1);
x_306 = lean_ctor_get(x_176, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_176);
x_307 = lean_ctor_get(x_177, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_177, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_177, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_177, 3);
lean_inc(x_310);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_311 = x_177;
} else {
 lean_dec_ref(x_177);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_306);
lean_ctor_set(x_314, 3, x_250);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
lean_ctor_set(x_1, 0, x_314);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_ctor_get(x_1, 2);
x_318 = lean_ctor_get(x_1, 3);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_1);
x_319 = lean_nat_dec_lt(x_2, x_316);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = lean_nat_dec_lt(x_316, x_2);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_317);
lean_dec(x_316);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_2);
lean_ctor_set(x_321, 2, x_3);
lean_ctor_set(x_321, 3, x_318);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_318, x_2, x_3);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_317);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
lean_object* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_318, x_2, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
return x_325;
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 2);
lean_inc(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_328);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_316);
lean_ctor_set(x_334, 2, x_317);
lean_ctor_set(x_334, 3, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_327, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
x_344 = 1;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_315);
lean_ctor_set(x_345, 1, x_316);
lean_ctor_set(x_345, 2, x_317);
lean_ctor_set(x_345, 3, x_326);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_338)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_338;
}
lean_ctor_set(x_346, 0, x_339);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_341);
lean_ctor_set(x_346, 3, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_337);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_325, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 2);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
x_351 = 0;
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(1, 4, 1);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_326);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_353, 0, x_315);
lean_ctor_set(x_353, 1, x_316);
lean_ctor_set(x_353, 2, x_317);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_358 = x_325;
} else {
 lean_dec_ref(x_325);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_326, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_326, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_326, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_363 = x_326;
} else {
 lean_dec_ref(x_326);
 x_363 = lean_box(0);
}
x_364 = 1;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_315);
lean_ctor_set(x_365, 1, x_316);
lean_ctor_set(x_365, 2, x_317);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_358;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set(x_366, 3, x_357);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_361);
lean_ctor_set(x_367, 3, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_325, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_325, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_325, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_371 = x_325;
} else {
 lean_dec_ref(x_325);
 x_371 = lean_box(0);
}
x_372 = 0;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_326);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_370);
lean_ctor_set(x_373, 3, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_316);
lean_ctor_set(x_374, 2, x_317);
lean_ctor_set(x_374, 3, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_325, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_325, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_378 = x_325;
} else {
 lean_dec_ref(x_325);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_368, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
lean_inc(x_326);
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_315);
lean_ctor_set(x_384, 1, x_316);
lean_ctor_set(x_384, 2, x_317);
lean_ctor_set(x_384, 3, x_326);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_385 = x_326;
} else {
 lean_dec_ref(x_326);
 x_385 = lean_box(0);
}
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_378)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_378;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_376);
lean_ctor_set(x_387, 2, x_377);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; 
x_388 = lean_ctor_get(x_325, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_325, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_390 = x_325;
} else {
 lean_dec_ref(x_325);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_326, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_326, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_326, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_326, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_395 = x_326;
} else {
 lean_dec_ref(x_326);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_391);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_393);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_388);
lean_ctor_set(x_398, 2, x_389);
lean_ctor_set(x_398, 3, x_368);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_315);
lean_ctor_set(x_399, 1, x_316);
lean_ctor_set(x_399, 2, x_317);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8_t x_400; 
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_315, x_2, x_3);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_316);
lean_ctor_set(x_402, 2, x_317);
lean_ctor_set(x_402, 3, x_318);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
lean_object* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_315, x_2, x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
return x_403;
}
else
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = 0;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set(x_410, 2, x_407);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_316);
lean_ctor_set(x_412, 2, x_317);
lean_ctor_set(x_412, 3, x_318);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8_t x_413; 
x_413 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_403, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_405, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 2);
lean_inc(x_419);
x_420 = lean_ctor_get(x_405, 3);
lean_inc(x_420);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_421 = x_405;
} else {
 lean_dec_ref(x_405);
 x_421 = lean_box(0);
}
x_422 = 1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_417);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean_is_scalar(x_416)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_416;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_316);
lean_ctor_set(x_424, 2, x_317);
lean_ctor_set(x_424, 3, x_318);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_418);
lean_ctor_set(x_425, 2, x_419);
lean_ctor_set(x_425, 3, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_403, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_403, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_428 = x_403;
} else {
 lean_dec_ref(x_403);
 x_428 = lean_box(0);
}
x_429 = 0;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_404);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_427);
lean_ctor_set(x_430, 3, x_405);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_316);
lean_ctor_set(x_431, 2, x_317);
lean_ctor_set(x_431, 3, x_318);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_403, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_403, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_403, 3);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_404, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_404, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_404, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_404, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_441 = x_404;
} else {
 lean_dec_ref(x_404);
 x_441 = lean_box(0);
}
x_442 = 1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set(x_443, 2, x_439);
lean_ctor_set(x_443, 3, x_440);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_436;
}
lean_ctor_set(x_444, 0, x_435);
lean_ctor_set(x_444, 1, x_316);
lean_ctor_set(x_444, 2, x_317);
lean_ctor_set(x_444, 3, x_318);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_403, 3);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_403, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_403, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_449 = x_403;
} else {
 lean_dec_ref(x_403);
 x_449 = lean_box(0);
}
x_450 = 0;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_447);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_316);
lean_ctor_set(x_452, 2, x_317);
lean_ctor_set(x_452, 3, x_318);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = lean_ctor_get_uint8(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_403, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_456 = x_403;
} else {
 lean_dec_ref(x_403);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_461 = x_446;
} else {
 lean_dec_ref(x_446);
 x_461 = lean_box(0);
}
lean_inc(x_404);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_457);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_463 = x_404;
} else {
 lean_dec_ref(x_404);
 x_463 = lean_box(0);
}
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_316);
lean_ctor_set(x_464, 2, x_317);
lean_ctor_set(x_464, 3, x_318);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 4, 1);
} else {
 x_465 = x_456;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_459);
lean_ctor_set(x_465, 3, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_403, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_403, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_468 = x_403;
} else {
 lean_dec_ref(x_403);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_404, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_404, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_404, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_473 = x_404;
} else {
 lean_dec_ref(x_404);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_469);
lean_ctor_set(x_474, 1, x_470);
lean_ctor_set(x_474, 2, x_471);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean_is_scalar(x_468)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_468;
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_466);
lean_ctor_set(x_476, 2, x_467);
lean_ctor_set(x_476, 3, x_446);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_316);
lean_ctor_set(x_477, 2, x_317);
lean_ctor_set(x_477, 3, x_318);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = level_mk_succ(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = level_mk_succ(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_12, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_13, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = level_mk_max(x_15, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = level_mk_max(x_15, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_25, x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_26, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = level_mk_imax(x_28, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = level_mk_imax(x_28, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
case 5:
{
lean_object* x_38; 
x_38 = l_Lean_TypeClass_Context_uMetaIdx(x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(x_42, x_40);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_2, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_47, x_42);
x_49 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_48);
x_50 = lean_name_mk_numeral(x_49, x_48);
x_51 = level_mk_mvar(x_50);
x_52 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_42, x_40, x_48);
lean_ctor_set(x_2, 1, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_2);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_54, x_42);
x_56 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_55);
x_57 = lean_name_mk_numeral(x_56, x_55);
x_58 = level_mk_mvar(x_57);
x_59 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_42, x_40, x_55);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_41);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
x_63 = l_Lean_TypeClass_Context_alphaMetaPrefix;
x_64 = lean_name_mk_numeral(x_63, x_62);
x_65 = level_mk_mvar(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_2);
return x_66;
}
}
}
default: 
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
return x_67;
}
}
}
}
lean_object* l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TypeClass_Context_uAlphaNormalizeCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_mmap___main___at_Lean_TypeClass_Context_eAlphaNormalizeCore___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_6, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_mmap___main___at_Lean_TypeClass_Context_eAlphaNormalizeCore___main___spec__1(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_9);
lean_ctor_set(x_11, 0, x_1);
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
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_17, x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mmap___main___at_Lean_TypeClass_Context_eAlphaNormalizeCore___main___spec__1(x_18, x_21);
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
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConst(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isFVar(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isApp(x_1);
if (x_5 == 0)
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_8, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_expr_mk_pi(x_6, x_7, x_11, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_expr_mk_pi(x_6, x_7, x_11, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_TypeClass_Context_eMetaIdx(x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(x_24, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_30, x_24);
x_32 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_31);
x_33 = lean_name_mk_numeral(x_32, x_31);
x_34 = lean_expr_mk_mvar(x_33);
x_35 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_24, x_23, x_31);
lean_ctor_set(x_2, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_2);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_37, x_24);
x_39 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_38);
x_40 = lean_name_mk_numeral(x_39, x_38);
x_41 = lean_expr_mk_mvar(x_40);
x_42 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_24, x_23, x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_25);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_45 = lean_ctor_get(x_26, 0);
lean_inc(x_45);
lean_dec(x_26);
x_46 = l_Lean_TypeClass_Context_alphaMetaPrefix;
x_47 = lean_name_mk_numeral(x_46, x_45);
x_48 = lean_expr_mk_mvar(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_2);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_box(0);
x_51 = l_Lean_Expr_getAppArgsAux___main(x_1, x_50);
x_52 = l_List_mmap___main___at_Lean_TypeClass_Context_eAlphaNormalizeCore___main___spec__1(x_51, x_2);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
x_56 = l_List_foldl___main___at_Lean_mkApp___spec__1(x_55, x_54);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
x_60 = l_List_foldl___main___at_Lean_mkApp___spec__1(x_59, x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
return x_62;
}
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
return x_63;
}
}
}
lean_object* l_Lean_TypeClass_Context_eAlphaNormalizeCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_Context__u03b1Norm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_TypeClass_Context__u03b1Norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_TypeClass_Context__u03b1Norm___closed__1;
x_3 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_PersistentArray_Default(lean_object*);
lean_object* initialize_Init_Lean_Expr(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeClass_Context(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_PersistentArray_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Expr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_MetavarContext(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_TypeClass_Context_Inhabited___closed__1 = _init_l_Lean_TypeClass_Context_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_Inhabited___closed__1);
l_Lean_TypeClass_Context_Inhabited = _init_l_Lean_TypeClass_Context_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_Context_Inhabited);
l_Lean_TypeClass_Context_metaPrefix___closed__1 = _init_l_Lean_TypeClass_Context_metaPrefix___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_metaPrefix___closed__1);
l_Lean_TypeClass_Context_metaPrefix___closed__2 = _init_l_Lean_TypeClass_Context_metaPrefix___closed__2();
lean_mark_persistent(l_Lean_TypeClass_Context_metaPrefix___closed__2);
l_Lean_TypeClass_Context_metaPrefix = _init_l_Lean_TypeClass_Context_metaPrefix();
lean_mark_persistent(l_Lean_TypeClass_Context_metaPrefix);
l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1 = _init_l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1);
l_Lean_TypeClass_Context_alphaMetaPrefix___closed__2 = _init_l_Lean_TypeClass_Context_alphaMetaPrefix___closed__2();
lean_mark_persistent(l_Lean_TypeClass_Context_alphaMetaPrefix___closed__2);
l_Lean_TypeClass_Context_alphaMetaPrefix = _init_l_Lean_TypeClass_Context_alphaMetaPrefix();
lean_mark_persistent(l_Lean_TypeClass_Context_alphaMetaPrefix);
l_Lean_TypeClass_Context_eInfer___closed__1 = _init_l_Lean_TypeClass_Context_eInfer___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_eInfer___closed__1);
l_Lean_TypeClass_Context_eInfer___closed__2 = _init_l_Lean_TypeClass_Context_eInfer___closed__2();
lean_mark_persistent(l_Lean_TypeClass_Context_eInfer___closed__2);
l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__1 = _init_l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__1();
lean_mark_persistent(l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__1);
l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__2 = _init_l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__2();
lean_mark_persistent(l_panicWithPos___at_Lean_TypeClass_Context_eAssign___spec__1___closed__2);
l_Lean_TypeClass_Context_eAssign___closed__1 = _init_l_Lean_TypeClass_Context_eAssign___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_eAssign___closed__1);
l_Lean_TypeClass_Context_eHasETmpMVar___closed__1 = _init_l_Lean_TypeClass_Context_eHasETmpMVar___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_eHasETmpMVar___closed__1);
l_Lean_TypeClass_Context_uAssign___closed__1 = _init_l_Lean_TypeClass_Context_uAssign___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_uAssign___closed__1);
l_Lean_TypeClass_Context_uHasTmpMVar___closed__1 = _init_l_Lean_TypeClass_Context_uHasTmpMVar___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_uHasTmpMVar___closed__1);
l_Lean_TypeClass_Context_uUnify___main___closed__1 = _init_l_Lean_TypeClass_Context_uUnify___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_uUnify___main___closed__1);
l_Lean_TypeClass_Context_uUnify___main___closed__2 = _init_l_Lean_TypeClass_Context_uUnify___main___closed__2();
lean_mark_persistent(l_Lean_TypeClass_Context_uUnify___main___closed__2);
l_Lean_TypeClass_Context_uUnify___main___closed__3 = _init_l_Lean_TypeClass_Context_uUnify___main___closed__3();
lean_mark_persistent(l_Lean_TypeClass_Context_uUnify___main___closed__3);
l_Lean_TypeClass_Context_uUnify___main___closed__4 = _init_l_Lean_TypeClass_Context_uUnify___main___closed__4();
lean_mark_persistent(l_Lean_TypeClass_Context_uUnify___main___closed__4);
l_Lean_TypeClass_Context_uUnify___main___closed__5 = _init_l_Lean_TypeClass_Context_uUnify___main___closed__5();
lean_mark_persistent(l_Lean_TypeClass_Context_uUnify___main___closed__5);
l_Lean_TypeClass_Context_eHasTmpMVar___closed__1 = _init_l_Lean_TypeClass_Context_eHasTmpMVar___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_eHasTmpMVar___closed__1);
l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___closed__1 = _init_l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___closed__1();
lean_mark_persistent(l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1___closed__1);
l_Lean_TypeClass_Context_eUnify___main___closed__1 = _init_l_Lean_TypeClass_Context_eUnify___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context_eUnify___main___closed__1);
l_Lean_TypeClass_Context_eUnify___main___closed__2 = _init_l_Lean_TypeClass_Context_eUnify___main___closed__2();
lean_mark_persistent(l_Lean_TypeClass_Context_eUnify___main___closed__2);
l_Lean_TypeClass_Context__u03b1Norm___closed__1 = _init_l_Lean_TypeClass_Context__u03b1Norm___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Context__u03b1Norm___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
