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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx(lean_object*);
lean_object* l_Lean_TypeClass_Context_eMetaIdx(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited;
lean_object* l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAssignIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
size_t l_USize_shift__right(size_t, size_t);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context__u03b1Norm(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_TypeClass_Context_alphaMetaPrefix___closed__1;
lean_object* l_Lean_TypeClass_Context_slowWhnfApp(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uMetaIdx___boxed(lean_object*);
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_TypeClass_Context_uShallowInstantiate(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_Context_eAssign___closed__1;
lean_object* l_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l_Lean_TypeClass_Context_uLookupIdx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main___closed__1;
lean_object* l_Lean_TypeClass_Context_uFind___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eAlphaNormalizeCore(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eLookupIdx___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasTmpMVar___boxed(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_PUnit_Inhabited;
uint8_t l_Lean_TypeClass_Context_uIsMeta(lean_object*);
lean_object* l_Lean_TypeClass_Context_Inhabited;
uint8_t l_Lean_TypeClass_Context_uFind___main(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
uint8_t l_Lean_TypeClass_Context_eFind___main(lean_object*, lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eIsMeta___boxed(lean_object*);
lean_object* l_Lean_TypeClass_Context_uIsMeta___boxed(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uInstantiate___main___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_TypeClass_Context_eInstantiate___main___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_TypeClass_Context_eUnify___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uUnify___main___closed__1;
lean_object* l_Lean_LevelToFormat_Level_format(lean_object*);
lean_object* l_Lean_Expr_bindingDomain(lean_object*);
lean_object* l_Lean_TypeClass_Context_uShallowInstantiate___main(lean_object*, lean_object*);
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
lean_object* l_Lean_TypeClass_Context_eInstantiate(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eMetaIdx___boxed(lean_object*);
lean_object* l_Lean_TypeClass_Context_eAssignIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_TypeClass_Context_eHasTmpMVar___spec__1(uint8_t, lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_updateApp_x21___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eInferIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___main___boxed(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uOccursIn___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_mvar(lean_object*);
lean_object* l_Lean_TypeClass_Context_eHasETmpMVar___boxed(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer___closed__1;
lean_object* level_mk_succ(lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInstantiate___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uAssignIdx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_TypeClass_Context_eLookupIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_uInstantiate___main(lean_object*, lean_object*);
uint8_t l_Lean_TypeClass_Context_uOccursIn(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer___closed__2;
uint8_t l_Lean_TypeClass_Context_uOccursIn___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eShallowInstantiate___main(lean_object*, lean_object*);
extern lean_object* l_Array_toPersistentArray___rarg___closed__1;
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_eInferIdx___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_TypeClass_Context_uHasTmpMVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_TypeClass_Context_uLookupIdx___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t lean_level_eq(lean_object*, lean_object*);
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
extern lean_object* l_Lean_exprIsInhabited___closed__1;
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
lean_object* l_Lean_TypeClass_Context_eShallowInstantiate___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_1 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_eShallowInstantiate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_eShallowInstantiate___main(x_1, x_2);
return x_3;
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
lean_object* _init_l_Lean_TypeClass_Context_eInfer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.TypeClass.Context");
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
x_5 = lean_unsigned_to_nat(70u);
x_6 = lean_unsigned_to_nat(14u);
x_7 = l_Lean_TypeClass_Context_eInfer___closed__2;
x_8 = l_panicWithPos___at_Lean_Expr_updateApp_x21___spec__1(x_4, x_5, x_6, x_7);
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
x_6 = lean_unsigned_to_nat(78u);
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
lean_object* l_Lean_TypeClass_Context_uShallowInstantiate___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_1 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_uShallowInstantiate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_Context_uShallowInstantiate___main(x_1, x_2);
return x_3;
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
x_6 = lean_unsigned_to_nat(128u);
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
x_3 = lean_level_eq(x_2, x_1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_115; 
x_4 = l_Lean_TypeClass_Context_uShallowInstantiate___main(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_TypeClass_Context_uShallowInstantiate___main(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_115 = l_Lean_TypeClass_Context_uIsMeta(x_8);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_10 = x_116;
goto block_114;
}
else
{
uint8_t x_117; 
x_117 = l_Lean_TypeClass_Context_uIsMeta(x_5);
if (x_117 == 0)
{
x_1 = x_8;
x_2 = x_5;
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_119; 
x_119 = lean_box(0);
x_10 = x_119;
goto block_114;
}
}
block_114:
{
lean_dec(x_10);
switch (lean_obj_tag(x_5)) {
case 0:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l_Lean_LevelToFormat_Level_format(x_5);
x_14 = l_Lean_Options_empty;
x_15 = l_Lean_Format_pretty(x_13, x_14);
x_16 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_LevelToFormat_Level_format(x_8);
x_21 = l_Lean_Format_pretty(x_20, x_14);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
case 1:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_1 = x_24;
x_2 = x_25;
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = l_Lean_LevelToFormat_Level_format(x_5);
x_28 = l_Lean_Options_empty;
x_29 = l_Lean_Format_pretty(x_27, x_28);
x_30 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_LevelToFormat_Level_format(x_8);
x_35 = l_Lean_Format_pretty(x_34, x_28);
x_36 = lean_string_append(x_33, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
case 2:
{
if (lean_obj_tag(x_8) == 2)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_5, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_dec(x_5);
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = l_Lean_TypeClass_Context_uUnify___main(x_38, x_40, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_1 = x_39;
x_2 = x_41;
x_3 = x_43;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_41);
lean_dec(x_39);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = l_Lean_LevelToFormat_Level_format(x_5);
x_50 = l_Lean_Options_empty;
x_51 = l_Lean_Format_pretty(x_49, x_50);
x_52 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_LevelToFormat_Level_format(x_8);
x_57 = l_Lean_Format_pretty(x_56, x_50);
x_58 = lean_string_append(x_55, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_9);
return x_59;
}
}
case 3:
{
if (lean_obj_tag(x_8) == 3)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_5, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_dec(x_5);
x_62 = lean_ctor_get(x_8, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_dec(x_8);
x_64 = l_Lean_TypeClass_Context_uUnify___main(x_60, x_62, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_1 = x_61;
x_2 = x_63;
x_3 = x_65;
goto _start;
}
else
{
uint8_t x_67; 
lean_dec(x_63);
lean_dec(x_61);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = l_Lean_LevelToFormat_Level_format(x_5);
x_72 = l_Lean_Options_empty;
x_73 = l_Lean_Format_pretty(x_71, x_72);
x_74 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = l_Lean_LevelToFormat_Level_format(x_8);
x_79 = l_Lean_Format_pretty(x_78, x_72);
x_80 = lean_string_append(x_77, x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_9);
return x_81;
}
}
case 4:
{
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_5, 0);
lean_inc(x_82);
lean_dec(x_5);
x_83 = lean_ctor_get(x_8, 0);
lean_inc(x_83);
lean_dec(x_8);
x_84 = lean_name_dec_eq(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lean_TypeClass_Context_uUnify___main___closed__3;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_9);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_9);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = l_Lean_LevelToFormat_Level_format(x_5);
x_90 = l_Lean_Options_empty;
x_91 = l_Lean_Format_pretty(x_89, x_90);
x_92 = l_Lean_TypeClass_Context_uUnify___main___closed__1;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_95 = lean_string_append(x_93, x_94);
x_96 = l_Lean_LevelToFormat_Level_format(x_8);
x_97 = l_Lean_Format_pretty(x_96, x_90);
x_98 = lean_string_append(x_95, x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_9);
return x_99;
}
}
default: 
{
lean_object* x_100; 
x_100 = l_Lean_TypeClass_Context_uMetaIdx(x_5);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = lean_level_eq(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_TypeClass_Context_uUnify___main___closed__4;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_9);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_9);
return x_105;
}
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec(x_100);
lean_inc(x_8);
x_107 = l_Lean_TypeClass_Context_uOccursIn(x_5, x_8);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = l_Lean_TypeClass_Context_uAssignIdx(x_106, x_8, x_9);
lean_dec(x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_106);
lean_dec(x_8);
x_112 = l_Lean_TypeClass_Context_uUnify___main___closed__5;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_9);
return x_113;
}
}
}
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
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_3, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_array_fget(x_1, x_3);
x_17 = lean_expr_instantiate1(x_13, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
x_4 = x_21;
goto block_12;
}
block_12:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_4);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_expr_mk_app(x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_8;
x_3 = x_10;
goto _start;
}
}
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_slowWhnfApp___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnfApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_slowWhnfApp___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnfApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_Context_slowWhnfApp(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_TypeClass_Context_slowWhnf___main(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isApp(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_3);
x_5 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_4);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_inc(x_1);
x_9 = l___private_Init_Lean_Expr_1__getAppArgsAux___main(x_1, x_6, x_8);
x_10 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
x_11 = l_Lean_TypeClass_Context_slowWhnf___main(x_10);
x_12 = l_Lean_TypeClass_Context_slowWhnfApp___main(x_9, x_11, x_3);
lean_dec(x_9);
return x_12;
}
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
lean_object* l_Nat_mforAux___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_sub(x_3, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = l_Lean_exprIsInhabited;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = lean_array_get(x_12, x_2, x_11);
lean_dec(x_11);
x_15 = l_Lean_TypeClass_Context_eUnify___main(x_13, x_14, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_4 = x_9;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
}
lean_object* l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_TypeClass_Context_uUnify___main(x_8, x_10, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_9;
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
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
lean_object* x_4; uint8_t x_190; 
x_190 = lean_expr_has_mvar(x_1);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = lean_expr_has_mvar(x_2);
if (x_191 == 0)
{
uint8_t x_192; 
x_192 = lean_expr_eqv(x_1, x_2);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_194 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_195 = lean_string_append(x_194, x_193);
lean_dec(x_193);
x_196 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_197 = lean_string_append(x_195, x_196);
x_198 = lean_expr_dbg_to_string(x_2);
lean_dec(x_2);
x_199 = lean_string_append(x_197, x_198);
lean_dec(x_198);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_3);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_3);
return x_202;
}
}
else
{
lean_object* x_203; 
x_203 = lean_box(0);
x_4 = x_203;
goto block_189;
}
}
else
{
lean_object* x_204; 
x_204 = lean_box(0);
x_4 = x_204;
goto block_189;
}
block_189:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_44; lean_object* x_115; lean_object* x_157; uint8_t x_169; 
lean_dec(x_4);
x_5 = l_Lean_TypeClass_Context_eShallowInstantiate___main(x_1, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_TypeClass_Context_slowWhnf___main(x_6);
x_9 = l_Lean_TypeClass_Context_eShallowInstantiate___main(x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_TypeClass_Context_slowWhnf___main(x_10);
x_169 = l_Lean_Expr_isMVar(x_8);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_TypeClass_Context_eIsMeta(x_12);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_box(0);
x_157 = x_171;
goto block_168;
}
else
{
uint8_t x_172; 
x_172 = l_Lean_TypeClass_Context_eIsMeta(x_8);
if (x_172 == 0)
{
x_1 = x_12;
x_2 = x_8;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_174; 
x_174 = lean_box(0);
x_157 = x_174;
goto block_168;
}
}
}
else
{
uint8_t x_175; 
x_175 = l_Lean_Expr_isMVar(x_12);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_TypeClass_Context_eIsMeta(x_12);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = lean_box(0);
x_157 = x_177;
goto block_168;
}
else
{
uint8_t x_178; 
x_178 = l_Lean_TypeClass_Context_eIsMeta(x_8);
if (x_178 == 0)
{
x_1 = x_12;
x_2 = x_8;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_180; 
x_180 = lean_box(0);
x_157 = x_180;
goto block_168;
}
}
}
else
{
uint8_t x_181; 
x_181 = lean_expr_eqv(x_8, x_12);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_Lean_TypeClass_Context_eIsMeta(x_12);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = lean_box(0);
x_157 = x_183;
goto block_168;
}
else
{
uint8_t x_184; 
x_184 = l_Lean_TypeClass_Context_eIsMeta(x_8);
if (x_184 == 0)
{
x_1 = x_12;
x_2 = x_8;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_186; 
x_186 = lean_box(0);
x_157 = x_186;
goto block_168;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_12);
lean_dec(x_8);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_11);
return x_188;
}
}
}
block_43:
{
uint8_t x_14; 
lean_dec(x_13);
x_14 = l_Lean_TypeClass_Context_eIsMeta(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_expr_dbg_to_string(x_8);
lean_dec(x_8);
x_16 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_expr_dbg_to_string(x_12);
lean_dec(x_12);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
uint8_t x_23; 
lean_inc(x_8);
lean_inc(x_12);
x_23 = l_Lean_TypeClass_Context_eOccursIn(x_12, x_8);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_TypeClass_Context_eMetaIdx(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_25 = l_Lean_TypeClass_Context_eInfer___closed__1;
x_26 = lean_unsigned_to_nat(228u);
x_27 = lean_unsigned_to_nat(20u);
x_28 = l_Lean_TypeClass_Context_eUnify___main___closed__2;
x_29 = l_panicWithPos___at_Lean_TypeClass_Context_eUnify___main___spec__1(x_25, x_26, x_27, x_28, x_11);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_TypeClass_Context_eAssignIdx(x_30, x_12, x_11);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_expr_dbg_to_string(x_8);
lean_dec(x_8);
x_36 = l_Lean_TypeClass_Context_eUnify___main___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_TypeClass_Context_uUnify___main___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_expr_dbg_to_string(x_12);
lean_dec(x_12);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
return x_42;
}
}
}
block_114:
{
uint8_t x_45; 
lean_dec(x_44);
x_45 = l_Lean_Expr_isApp(x_8);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_isForall(x_8);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_13 = x_47;
goto block_43;
}
else
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isForall(x_12);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_13 = x_49;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = l_Lean_Expr_bindingDomain(x_8);
x_51 = l_Lean_Expr_bindingDomain(x_12);
x_52 = l_Lean_TypeClass_Context_eUnify___main(x_50, x_51, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Expr_bindingBody(x_8);
lean_dec(x_8);
x_55 = l_Lean_Expr_bindingBody(x_12);
lean_dec(x_12);
x_1 = x_54;
x_2 = x_55;
x_3 = x_53;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
else
{
uint8_t x_61; 
x_61 = l_Lean_Expr_isApp(x_12);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isForall(x_8);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_13 = x_63;
goto block_43;
}
else
{
uint8_t x_64; 
x_64 = l_Lean_Expr_isForall(x_12);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_13 = x_65;
goto block_43;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = l_Lean_Expr_bindingDomain(x_8);
x_67 = l_Lean_Expr_bindingDomain(x_12);
x_68 = l_Lean_TypeClass_Context_eUnify___main(x_66, x_67, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Expr_bindingBody(x_8);
lean_dec(x_8);
x_71 = l_Lean_Expr_bindingBody(x_12);
lean_dec(x_12);
x_1 = x_70;
x_2 = x_71;
x_3 = x_69;
goto _start;
}
else
{
uint8_t x_73; 
lean_dec(x_12);
lean_dec(x_8);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 0);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_68);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Expr_getAppNumArgsAux___main(x_8, x_77);
x_79 = l_Lean_Expr_getAppNumArgsAux___main(x_12, x_77);
x_80 = lean_nat_dec_eq(x_78, x_79);
if (x_80 == 0)
{
uint8_t x_81; 
lean_dec(x_79);
lean_dec(x_78);
x_81 = l_Lean_Expr_isForall(x_8);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_13 = x_82;
goto block_43;
}
else
{
uint8_t x_83; 
x_83 = l_Lean_Expr_isForall(x_12);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
x_13 = x_84;
goto block_43;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = l_Lean_Expr_bindingDomain(x_8);
x_86 = l_Lean_Expr_bindingDomain(x_12);
x_87 = l_Lean_TypeClass_Context_eUnify___main(x_85, x_86, x_11);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Expr_bindingBody(x_8);
lean_dec(x_8);
x_90 = l_Lean_Expr_bindingBody(x_12);
lean_dec(x_12);
x_1 = x_89;
x_2 = x_90;
x_3 = x_88;
goto _start;
}
else
{
uint8_t x_92; 
lean_dec(x_12);
lean_dec(x_8);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_96 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_78);
x_97 = lean_mk_array(x_78, x_96);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_78, x_98);
lean_dec(x_78);
lean_inc(x_8);
x_100 = l___private_Init_Lean_Expr_1__getAppArgsAux___main(x_8, x_97, x_99);
lean_inc(x_79);
x_101 = lean_mk_array(x_79, x_96);
x_102 = lean_nat_sub(x_79, x_98);
lean_dec(x_79);
lean_inc(x_12);
x_103 = l___private_Init_Lean_Expr_1__getAppArgsAux___main(x_12, x_101, x_102);
x_104 = l_Lean_Expr_getAppFn___main(x_8);
lean_dec(x_8);
x_105 = l_Lean_Expr_getAppFn___main(x_12);
lean_dec(x_12);
x_106 = l_Lean_TypeClass_Context_eUnify___main(x_104, x_105, x_11);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_array_get_size(x_100);
lean_inc(x_108);
x_109 = l_Nat_mforAux___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(x_100, x_103, x_108, x_108, x_107);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_100);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_103);
lean_dec(x_100);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 0);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_106);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
}
block_156:
{
uint8_t x_116; 
lean_dec(x_115);
x_116 = l_Lean_Expr_isFVar(x_8);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l_Lean_Expr_isConst(x_8);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_box(0);
x_44 = x_118;
goto block_114;
}
else
{
uint8_t x_119; 
x_119 = l_Lean_Expr_isConst(x_12);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_box(0);
x_44 = x_120;
goto block_114;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = l_Lean_Expr_constName(x_8);
x_122 = l_Lean_Expr_constName(x_12);
x_123 = lean_name_dec_eq(x_121, x_122);
lean_dec(x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_box(0);
x_44 = x_124;
goto block_114;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l_Lean_Expr_constLevels(x_8);
lean_dec(x_8);
x_126 = l_Lean_Expr_constLevels(x_12);
lean_dec(x_12);
x_127 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_125, x_126, x_11);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
x_128 = l_Lean_Expr_isFVar(x_12);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = l_Lean_Expr_isConst(x_8);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_box(0);
x_44 = x_130;
goto block_114;
}
else
{
uint8_t x_131; 
x_131 = l_Lean_Expr_isConst(x_12);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
x_44 = x_132;
goto block_114;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = l_Lean_Expr_constName(x_8);
x_134 = l_Lean_Expr_constName(x_12);
x_135 = lean_name_dec_eq(x_133, x_134);
lean_dec(x_134);
lean_dec(x_133);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_44 = x_136;
goto block_114;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Lean_Expr_constLevels(x_8);
lean_dec(x_8);
x_138 = l_Lean_Expr_constLevels(x_12);
lean_dec(x_12);
x_139 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_137, x_138, x_11);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Expr_fvarName(x_8);
x_141 = l_Lean_Expr_fvarName(x_12);
x_142 = lean_name_dec_eq(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_Lean_Expr_isConst(x_8);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_box(0);
x_44 = x_144;
goto block_114;
}
else
{
uint8_t x_145; 
x_145 = l_Lean_Expr_isConst(x_12);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_box(0);
x_44 = x_146;
goto block_114;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Expr_constName(x_8);
x_148 = l_Lean_Expr_constName(x_12);
x_149 = lean_name_dec_eq(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_box(0);
x_44 = x_150;
goto block_114;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = l_Lean_Expr_constLevels(x_8);
lean_dec(x_8);
x_152 = l_Lean_Expr_constLevels(x_12);
lean_dec(x_12);
x_153 = l_List_mfor_u2082___main___at_Lean_TypeClass_Context_eUnify___main___spec__3(x_151, x_152, x_11);
return x_153;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_12);
lean_dec(x_8);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_11);
return x_155;
}
}
}
}
block_168:
{
uint8_t x_158; 
lean_dec(x_157);
x_158 = l_Lean_Expr_isBVar(x_8);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_box(0);
x_115 = x_159;
goto block_156;
}
else
{
uint8_t x_160; 
x_160 = l_Lean_Expr_isBVar(x_12);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_box(0);
x_115 = x_161;
goto block_156;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = l_Lean_Expr_bvarIdx(x_8);
x_163 = l_Lean_Expr_bvarIdx(x_12);
x_164 = lean_nat_dec_eq(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_box(0);
x_115 = x_165;
goto block_156;
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_12);
lean_dec(x_8);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_11);
return x_167;
}
}
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
lean_object* l_Nat_mforAux___main___at_Lean_TypeClass_Context_eUnify___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_TypeClass_Context_eUnify___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_31, x_2, x_3);
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
lean_object* x_176; lean_object* x_177; 
x_176 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_28, x_2, x_3);
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
lean_object* x_325; lean_object* x_326; 
x_325 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_318, x_2, x_3);
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
lean_object* x_403; lean_object* x_404; 
x_403 = l_RBNode_ins___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__3(x_315, x_2, x_3);
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
uint8_t x_3; 
x_3 = l_Lean_Level_hasMVar___main(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = level_mk_succ(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = level_mk_succ(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_14, x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_15, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = level_mk_max(x_17, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = level_mk_max(x_17, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_27, x_2);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_TypeClass_Context_uAlphaNormalizeCore___main(x_28, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = level_mk_imax(x_30, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = level_mk_imax(x_30, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
case 5:
{
lean_object* x_40; 
x_40 = l_Lean_TypeClass_Context_uMetaIdx(x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_2, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_49, x_44);
x_51 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_50);
x_52 = lean_name_mk_numeral(x_51, x_50);
x_53 = level_mk_mvar(x_52);
x_54 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_44, x_42, x_50);
lean_ctor_set(x_2, 1, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_2);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_56, x_44);
x_58 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_57);
x_59 = lean_name_mk_numeral(x_58, x_57);
x_60 = level_mk_mvar(x_59);
x_61 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_44, x_42, x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_65 = l_Lean_TypeClass_Context_alphaMetaPrefix;
x_66 = lean_name_mk_numeral(x_65, x_64);
x_67 = level_mk_mvar(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_2);
return x_68;
}
}
}
default: 
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_2);
return x_69;
}
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
x_5 = lean_expr_has_mvar(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_7, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_8, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_expr_mk_app(x_10, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_expr_mk_app(x_10, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
case 7:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_22, x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_TypeClass_Context_eAlphaNormalizeCore___main(x_23, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_expr_mk_pi(x_20, x_21, x_25, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_expr_mk_pi(x_20, x_21, x_25, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
default: 
{
lean_object* x_35; 
x_35 = l_Lean_TypeClass_Context_eMetaIdx(x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = l_RBNode_find___main___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__1(x_38, x_37);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_2, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 0);
lean_dec(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_44, x_38);
x_46 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_45);
x_47 = lean_name_mk_numeral(x_46, x_45);
x_48 = lean_expr_mk_mvar(x_47);
x_49 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_38, x_37, x_45);
lean_ctor_set(x_2, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_51, x_38);
x_53 = l_Lean_TypeClass_Context_alphaMetaPrefix;
lean_inc(x_52);
x_54 = lean_name_mk_numeral(x_53, x_52);
x_55 = lean_expr_mk_mvar(x_54);
x_56 = l_RBNode_insert___at_Lean_TypeClass_Context_uAlphaNormalizeCore___main___spec__2(x_38, x_37, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_39);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_59 = lean_ctor_get(x_40, 0);
lean_inc(x_59);
lean_dec(x_40);
x_60 = l_Lean_TypeClass_Context_alphaMetaPrefix;
x_61 = lean_name_mk_numeral(x_60, x_59);
x_62 = lean_expr_mk_mvar(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_2);
return x_63;
}
}
}
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_2);
return x_64;
}
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_2);
return x_65;
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
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_PersistentArray_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
