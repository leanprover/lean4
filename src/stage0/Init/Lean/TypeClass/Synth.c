// Lean compiler output
// Module: Init.Lean.TypeClass.Synth
// Imports: Init.Lean.Expr Init.Lean.Environment Init.Lean.Class Init.Lean.MetavarContext Init.Lean.TypeClass.Context Init.Data.PersistentHashMap.Default Init.Data.Stack.Default Init.Data.Queue.Default
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
lean_object* l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__2;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_introduceLocals(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_TypeClass_synth___closed__2;
lean_object* l_Lean_Expr_constName(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInfer(lean_object*, lean_object*);
lean_object* l_Array_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synthCore___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synthCore___main(lean_object*, lean_object*);
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l_Array_back___at_Lean_TypeClass_consume___spec__2___boxed(lean_object*);
size_t l_USize_shift__right(size_t, size_t);
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_ConsumerNode_Inhabited;
lean_object* l_Lean_TypeClass_Context__u03b1Norm(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Queue_enqueue___rarg(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_introduceLocals___main___closed__2;
uint8_t l_Lean_Level_hasMVar___main(lean_object*);
lean_object* l_Lean_TypeClass_newAnswer(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synthCore___main___closed__1;
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_wakeUp(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_Inhabited___closed__1;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_back___at_Lean_TypeClass_generate___spec__2(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___boxed(lean_object*);
lean_object* l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
lean_object* l_Lean_TypeClass_Context_uNewMeta(lean_object*);
lean_object* l_Stack_pop___at_Lean_TypeClass_consume___spec__3(lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_HasToString___boxed(lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
extern lean_object* l_Lean_formatDataValue___closed__1;
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_newSubgoal___spec__5(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_Inhabited;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_preprocessForOutParams___closed__1;
lean_object* l_Lean_TypeClass_step(lean_object*);
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1(lean_object*);
lean_object* l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_TypeClass_wakeUp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_quickIsClass___main(lean_object*, lean_object*);
extern lean_object* l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_constNameToTypedExpr___closed__1;
lean_object* l_Lean_TypeClass_synthCore___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_miterateAux___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_TypeClass_quickIsClass___main___closed__1;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Node_Inhabited___closed__1;
extern lean_object* l_Lean_TypeClass_Context_Inhabited;
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_constNameToTypedExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synthCore(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Node_Inhabited;
lean_object* l_Lean_TypeClass_resume___closed__1;
lean_object* l_Lean_TypeClass_synth___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___rarg___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_TypeClass_introduceLocals___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_introduceLocals___main___closed__1;
uint8_t l_Lean_TypeClass_Context_eHasTmpMVar(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__2;
lean_object* l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_has_out_params(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_generate(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1(lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1___boxed(lean_object*);
lean_object* l_Lean_TypeClass_GeneratorNode_Inhabited;
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_introduceMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_TypeClass_collectUReplacements(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_TypeClass_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_consume___closed__2;
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal___closed__2;
lean_object* l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Queue_isEmpty___rarg(lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newConsumerNode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInstantiate___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_generate___closed__1;
lean_object* l_Array_pop(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal___closed__3;
lean_object* l_Lean_TypeClass_preprocessForOutParams(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_consume___closed__1;
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__1;
lean_object* l_Lean_TypeClass_resume___closed__2;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Queue_dequeue_x3f___rarg(lean_object*);
lean_object* lean_get_class_instances(lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_consume(lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synth(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_HasToString(lean_object*);
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1___boxed(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_newSubgoal___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels(lean_object*);
lean_object* l_Stack_modify___at_Lean_TypeClass_generate___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_introduceMVars___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_mvar(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Stack_pop___at_Lean_TypeClass_generate___spec__3(lean_object*);
lean_object* l_Lean_TypeClass_generate___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal___closed__1;
lean_object* l_Lean_TypeClass_Context_eNewMeta(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_TypeClass_resume(lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_Lean_TypeClass_collectUReplacements___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newAnswer___closed__1;
lean_object* l_List_foldl___main___at_Lean_TypeClass_constNameToTypedExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_TypeClass_consume___spec__2(lean_object*);
lean_object* l_Lean_TypeClass_quickIsClass(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_TypeClass_newAnswer___closed__2;
lean_object* l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TypeClass_step___closed__1;
lean_object* l_Lean_TypeClass_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* l_Array_back___at_Lean_TypeClass_generate___spec__2___boxed(lean_object*);
lean_object* l_Lean_TypeClass_synth___closed__3;
lean_object* l_Lean_TypeClass_constNameToTypedExpr___closed__2;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* _init_l_Lean_TypeClass_TypedExpr_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TypedExpr(");
return x_1;
}
}
lean_object* l_Lean_TypeClass_TypedExpr_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_expr_dbg_to_string(x_2);
x_5 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_expr_dbg_to_string(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_TypeClass_TypedExpr_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_TypedExpr_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_TypeClass_TypedExpr_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_exprIsInhabited___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_TypeClass_TypedExpr_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_TypedExpr_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_Node_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_exprIsInhabited___closed__1;
x_2 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_3 = l_Lean_TypeClass_TypedExpr_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_TypeClass_Node_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_Node_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TypeClass_Node_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_ConsumerNode_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TypeClass_Node_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_GeneratorNode_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_quickIsClass___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_TypeClass_quickIsClass___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
x_4 = lean_is_class(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Expr_getAppFn___main(x_8);
lean_dec(x_8);
x_10 = l_Lean_Expr_isConst(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = l_Lean_Expr_isLambda(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_TypeClass_quickIsClass___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Expr_constName(x_9);
lean_inc(x_14);
x_15 = lean_is_class(x_1, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = l_Lean_Expr_isLambda(x_9);
lean_dec(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_TypeClass_quickIsClass___main___closed__1;
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
case 7:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
case 8:
{
lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
case 10:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_2 = x_24;
goto _start;
}
case 11:
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
return x_26;
}
default: 
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_TypeClass_quickIsClass___main___closed__1;
return x_27;
}
}
}
}
lean_object* l_Lean_TypeClass_quickIsClass(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_quickIsClass___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(lean_object* x_1) {
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_TypeClass_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_newSubgoal___spec__5(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_expr_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_TypeClass_newSubgoal___spec__4(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_miterateAux___main___at_Lean_TypeClass_newSubgoal___spec__5(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
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
lean_object* l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_expr_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_expr_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* _init_l_Lean_TypeClass_newSubgoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quickIsClass not sufficient to show `");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_newSubgoal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("` is a class");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_newSubgoal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("found non-class goal `");
return x_1;
}
}
lean_object* l_Lean_TypeClass_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
lean_inc(x_2);
x_9 = l_Lean_TypeClass_Context_eInfer(x_2, x_4);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 6);
lean_inc(x_16);
lean_inc(x_9);
lean_inc(x_10);
x_17 = l_Lean_TypeClass_quickIsClass___main(x_10, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_19 = l_Lean_TypeClass_newSubgoal___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_TypeClass_newSubgoal___closed__2;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_25 = l_Lean_TypeClass_newSubgoal___closed__3;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_formatDataValue___closed__1;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_30 = lean_ctor_get(x_7, 6);
lean_dec(x_30);
x_31 = lean_ctor_get(x_7, 5);
lean_dec(x_31);
x_32 = lean_ctor_get(x_7, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_7, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_7, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_7, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
lean_dec(x_23);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_9);
lean_inc(x_3);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_10);
x_40 = lean_get_class_instances(x_10, x_37);
x_41 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_mkOptionalNode___rarg___closed__1;
x_44 = lean_array_push(x_43, x_1);
x_45 = l_Array_empty___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_push(x_13, x_42);
x_48 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_16, x_3, x_46);
lean_ctor_set(x_7, 6, x_48);
lean_ctor_set(x_7, 3, x_47);
x_49 = lean_box(0);
lean_ctor_set(x_5, 0, x_49);
return x_5;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_7);
x_50 = lean_ctor_get(x_23, 0);
lean_inc(x_50);
lean_dec(x_23);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_9);
lean_inc(x_3);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_2);
lean_ctor_set(x_52, 2, x_51);
lean_inc(x_10);
x_53 = lean_get_class_instances(x_10, x_50);
x_54 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_mkOptionalNode___rarg___closed__1;
x_57 = lean_array_push(x_56, x_1);
x_58 = l_Array_empty___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_13, x_55);
x_61 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_16, x_3, x_59);
x_62 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_11);
lean_ctor_set(x_62, 2, x_12);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_14);
lean_ctor_set(x_62, 5, x_15);
lean_ctor_set(x_62, 6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_5, 1, x_62);
lean_ctor_set(x_5, 0, x_63);
return x_5;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_5, 1);
lean_inc(x_64);
lean_dec(x_5);
lean_inc(x_2);
x_65 = l_Lean_TypeClass_Context_eInfer(x_2, x_4);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 6);
lean_inc(x_72);
lean_inc(x_65);
lean_inc(x_66);
x_73 = l_Lean_TypeClass_quickIsClass___main(x_66, x_65);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_expr_dbg_to_string(x_65);
lean_dec(x_65);
x_75 = l_Lean_TypeClass_newSubgoal___closed__1;
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = l_Lean_TypeClass_newSubgoal___closed__2;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_64);
return x_79;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_expr_dbg_to_string(x_65);
lean_dec(x_65);
x_82 = l_Lean_TypeClass_newSubgoal___closed__3;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Lean_formatDataValue___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_64);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 lean_ctor_release(x_64, 5);
 lean_ctor_release(x_64, 6);
 x_87 = x_64;
} else {
 lean_dec_ref(x_64);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_80, 0);
lean_inc(x_88);
lean_dec(x_80);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_4);
lean_ctor_set(x_89, 1, x_65);
lean_inc(x_3);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_3);
lean_ctor_set(x_90, 1, x_2);
lean_ctor_set(x_90, 2, x_89);
lean_inc(x_66);
x_91 = lean_get_class_instances(x_66, x_88);
x_92 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_mkOptionalNode___rarg___closed__1;
x_95 = lean_array_push(x_94, x_1);
x_96 = l_Array_empty___closed__1;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_69, x_93);
x_99 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_72, x_3, x_97);
if (lean_is_scalar(x_87)) {
 x_100 = lean_alloc_ctor(0, 7, 0);
} else {
 x_100 = x_87;
}
lean_ctor_set(x_100, 0, x_66);
lean_ctor_set(x_100, 1, x_67);
lean_ctor_set(x_100, 2, x_68);
lean_ctor_set(x_100, 3, x_98);
lean_ctor_set(x_100, 4, x_70);
lean_ctor_set(x_100, 5, x_71);
lean_ctor_set(x_100, 6, x_99);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_newSubgoal___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_miterateAux___main___at_Lean_TypeClass_newSubgoal___spec__5(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_TypeClass_introduceMVars___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
if (lean_obj_tag(x_5) == 7)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_LocalContext_mkForall(x_1, x_2, x_13);
x_16 = l_Lean_TypeClass_Context_eNewMeta(x_15, x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_20 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_2, x_2, x_19, x_17);
lean_inc(x_20);
x_21 = lean_expr_mk_app(x_4, x_20);
x_22 = lean_expr_instantiate1(x_14, x_20);
x_23 = l_Lean_BinderInfo_isInstImplicit(x_12);
if (x_23 == 0)
{
lean_dec(x_17);
x_3 = x_18;
x_4 = x_21;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_25; 
x_25 = lean_array_push(x_6, x_17);
x_3 = x_18;
x_4 = x_21;
x_5 = x_22;
x_6 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_7 = x_27;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_TypeClass_introduceMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_TypeClass_introduceMVars___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_TypeClass_introduceLocals___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tmp");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_introduceLocals___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TypeClass_introduceLocals___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_introduceLocals___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_TypeClass_introduceLocals___main___closed__2;
lean_inc(x_1);
x_10 = lean_name_mk_numeral(x_9, x_1);
lean_inc(x_10);
x_11 = lean_local_ctx_mk_local_decl(x_2, x_10, x_5, x_7, x_6);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_expr_mk_fvar(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
lean_inc(x_13);
x_16 = lean_array_push(x_3, x_13);
x_17 = lean_expr_instantiate1(x_8, x_13);
x_1 = x_15;
x_2 = x_12;
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_TypeClass_introduceLocals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_TypeClass_introduceLocals___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_TypeClass_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_LocalContext_Inhabited___closed__1;
x_11 = l_Array_empty___closed__1;
x_12 = l_Lean_TypeClass_introduceLocals___main(x_9, x_10, x_11, x_6);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_16);
lean_inc(x_14);
x_17 = l_Lean_TypeClass_introduceMVars___main(x_14, x_16, x_1, x_7, x_8, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = l_Lean_LocalContext_mkLambda(x_14, x_16, x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_28 = l_Lean_TypeClass_Context_eUnify___main(x_15, x_23, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_26);
x_31 = l_Lean_TypeClass_Context_eUnify___main(x_5, x_25, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = l_Array_toList___rarg(x_24);
lean_dec(x_24);
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_4, 0, x_36);
return x_4;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_dec(x_4);
x_38 = l_Array_toList___rarg(x_24);
lean_dec(x_24);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_19, 0, x_32);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_19);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_31);
lean_free_object(x_19);
lean_dec(x_24);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_4, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_4, 0, x_43);
return x_4;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_26);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_TypeClass_Context_eUnify___main(x_5, x_25, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_52 = x_4;
} else {
 lean_dec_ref(x_4);
 x_52 = lean_box(0);
}
x_53 = l_Array_toList___rarg(x_24);
lean_dec(x_24);
lean_ctor_set(x_19, 1, x_53);
lean_ctor_set(x_19, 0, x_50);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_19);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
lean_free_object(x_19);
lean_dec(x_24);
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_57 = x_4;
} else {
 lean_dec_ref(x_4);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_28);
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_4, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_4, 0, x_62);
return x_4;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
lean_dec(x_4);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_19, 0);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_19);
x_68 = l_Lean_LocalContext_mkLambda(x_14, x_16, x_21);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_20);
x_71 = l_Lean_TypeClass_Context_eUnify___main(x_15, x_66, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_TypeClass_Context_eUnify___main(x_5, x_68, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_78 = x_4;
} else {
 lean_dec_ref(x_4);
 x_78 = lean_box(0);
}
x_79 = l_Array_toList___rarg(x_67);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_75);
lean_dec(x_67);
x_83 = lean_ctor_get(x_4, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_84 = x_4;
} else {
 lean_dec_ref(x_4);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_88 = x_4;
} else {
 lean_dec_ref(x_4);
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
}
}
lean_object* l_Lean_TypeClass_newConsumerNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 4);
x_13 = lean_array_push(x_12, x_10);
lean_ctor_set(x_8, 4, x_13);
x_14 = lean_box(0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_22 = lean_array_push(x_19, x_10);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
x_24 = lean_box(0);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 6);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
x_35 = lean_array_push(x_31, x_26);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 7, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_30);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_32);
lean_ctor_set(x_36, 6, x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_42 = x_4;
} else {
 lean_dec_ref(x_4);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 6);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
x_53 = lean_array_push(x_49, x_44);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 7, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_50);
lean_ctor_set(x_54, 6, x_51);
x_55 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_42;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
lean_object* _init_l_Lean_TypeClass_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume found nothing to resume");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_resume___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume found no remaining subgoals");
return x_1;
}
}
lean_object* l_Lean_TypeClass_resume(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
x_6 = l_Queue_dequeue_x3f___rarg(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_TypeClass_resume___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
lean_inc(x_3);
lean_ctor_set(x_1, 0, x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
lean_dec(x_8);
x_13 = l_Lean_TypeClass_resume___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_inc(x_20);
x_21 = l_Lean_TypeClass_Context_eInfer(x_20, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_TypeClass_tryResolve(x_20, x_22, x_16, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_25, 5);
lean_dec(x_28);
lean_ctor_set(x_25, 5, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_ctor_set(x_23, 0, x_9);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_List_append___rarg(x_31, x_18);
x_33 = l_Lean_TypeClass_newConsumerNode(x_19, x_30, x_32, x_23);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
x_37 = lean_ctor_get(x_25, 2);
x_38 = lean_ctor_get(x_25, 3);
x_39 = lean_ctor_get(x_25, 4);
x_40 = lean_ctor_get(x_25, 6);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_39);
lean_ctor_set(x_41, 5, x_15);
lean_ctor_set(x_41, 6, x_40);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_9);
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_List_append___rarg(x_44, x_18);
x_46 = l_Lean_TypeClass_newConsumerNode(x_19, x_43, x_45, x_23);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_23, 1);
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_47);
lean_inc(x_48);
lean_dec(x_23);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 6);
lean_inc(x_54);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 lean_ctor_release(x_47, 6);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 7, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_53);
lean_ctor_set(x_56, 5, x_15);
lean_ctor_set(x_56, 6, x_54);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_57; 
lean_dec(x_19);
lean_dec(x_18);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_9);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_9);
lean_ctor_set(x_59, 1, x_56);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_List_append___rarg(x_61, x_18);
x_63 = l_Lean_TypeClass_newConsumerNode(x_19, x_60, x_62, x_59);
return x_63;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 5);
lean_inc(x_65);
x_66 = l_Queue_dequeue_x3f___rarg(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_TypeClass_resume___closed__1;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_box(0);
lean_inc(x_64);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
x_75 = l_Lean_TypeClass_resume___closed__2;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_64);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_64);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_inc(x_82);
x_83 = l_Lean_TypeClass_Context_eInfer(x_82, x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_TypeClass_tryResolve(x_82, x_84, x_78, x_71);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 6);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 lean_ctor_release(x_86, 6);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 7, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_92);
lean_ctor_set(x_96, 4, x_93);
lean_ctor_set(x_96, 5, x_77);
lean_ctor_set(x_96, 6, x_94);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_97; 
lean_dec(x_81);
lean_dec(x_80);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_70);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
lean_dec(x_87);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_70);
lean_ctor_set(x_99, 1, x_96);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = l_List_append___rarg(x_101, x_80);
x_103 = l_Lean_TypeClass_newConsumerNode(x_81, x_100, x_102, x_99);
return x_103;
}
}
}
}
}
}
lean_object* l_Lean_TypeClass_wakeUp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_1);
x_11 = l_Queue_enqueue___rarg(x_10, x_9);
lean_ctor_set(x_5, 5, x_11);
x_12 = lean_box(0);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
x_17 = lean_ctor_get(x_5, 3);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_5, 5);
x_20 = lean_ctor_get(x_5, 6);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
lean_inc(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_1);
x_22 = l_Queue_enqueue___rarg(x_21, x_19);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_23, 6, x_20);
x_24 = lean_box(0);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_24);
return x_3;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 6);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
lean_inc(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_1);
x_36 = l_Queue_enqueue___rarg(x_35, x_32);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 7, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_31);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_41, 1, x_45);
x_46 = lean_box(0);
lean_ctor_set(x_3, 0, x_46);
return x_3;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 2);
x_49 = lean_ctor_get(x_41, 3);
x_50 = lean_ctor_get(x_41, 4);
x_51 = lean_ctor_get(x_41, 5);
x_52 = lean_ctor_get(x_41, 6);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_1);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_49);
lean_ctor_set(x_54, 4, x_50);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set(x_54, 6, x_52);
x_55 = lean_box(0);
lean_ctor_set(x_3, 1, x_54);
lean_ctor_set(x_3, 0, x_55);
return x_3;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
lean_dec(x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 6);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_1);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 7, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_59);
lean_ctor_set(x_65, 4, x_60);
lean_ctor_set(x_65, 5, x_61);
lean_ctor_set(x_65, 6, x_62);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
lean_object* l_Lean_TypeClass_wakeUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeClass_wakeUp(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_expr_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_expr_eqv(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
lean_inc(x_1);
x_16 = l_Lean_TypeClass_wakeUp(x_1, x_13, x_4);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
x_3 = x_15;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_3 = x_15;
x_4 = x_23;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_TypeClass_newAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[newAnswer]: ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_newAnswer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" not found in table!");
return x_1;
}
}
lean_object* l_Lean_TypeClass_newAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 6);
lean_inc(x_13);
x_14 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_15 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_16 = l_Lean_TypeClass_newAnswer___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_TypeClass_newAnswer___closed__2;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4(x_2, x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_5, 6);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
lean_inc(x_2);
x_34 = lean_array_push(x_23, x_2);
lean_inc(x_22);
lean_ctor_set(x_20, 1, x_34);
x_35 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_13, x_1, x_20);
lean_ctor_set(x_5, 6, x_35);
x_36 = lean_box(0);
lean_ctor_set(x_3, 0, x_36);
x_37 = l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_2, x_22, x_24, x_3);
lean_dec(x_22);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
lean_inc(x_2);
x_38 = lean_array_push(x_23, x_2);
lean_inc(x_22);
lean_ctor_set(x_20, 1, x_38);
x_39 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_13, x_1, x_20);
x_40 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_8);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_11);
lean_ctor_set(x_40, 5, x_12);
lean_ctor_set(x_40, 6, x_39);
x_41 = lean_box(0);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_3, 0, x_41);
x_42 = l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_2, x_22, x_24, x_3);
lean_dec(x_22);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_free_object(x_20);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
lean_ctor_set(x_3, 0, x_43);
return x_3;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4(x_2, x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_48 = x_5;
} else {
 lean_dec_ref(x_5);
 x_48 = lean_box(0);
}
lean_inc(x_2);
x_49 = lean_array_push(x_45, x_2);
lean_inc(x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_13, x_1, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 7, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_7);
lean_ctor_set(x_52, 1, x_8);
lean_ctor_set(x_52, 2, x_9);
lean_ctor_set(x_52, 3, x_10);
lean_ctor_set(x_52, 4, x_11);
lean_ctor_set(x_52, 5, x_12);
lean_ctor_set(x_52, 6, x_51);
x_53 = lean_box(0);
lean_ctor_set(x_3, 1, x_52);
lean_ctor_set(x_3, 0, x_53);
x_54 = l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_2, x_44, x_46, x_3);
lean_dec(x_44);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_3, 0, x_55);
return x_3;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
lean_dec(x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 6);
lean_inc(x_63);
x_64 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_63, x_1);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_65 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_66 = l_Lean_TypeClass_newAnswer___closed__1;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = l_Lean_TypeClass_newAnswer___closed__2;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_56);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
lean_dec(x_64);
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
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4(x_2, x_73, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 x_77 = x_56;
} else {
 lean_dec_ref(x_56);
 x_77 = lean_box(0);
}
lean_inc(x_2);
x_78 = lean_array_push(x_73, x_2);
lean_inc(x_72);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_63, x_1, x_79);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_57);
lean_ctor_set(x_81, 1, x_58);
lean_ctor_set(x_81, 2, x_59);
lean_ctor_set(x_81, 3, x_60);
lean_ctor_set(x_81, 4, x_61);
lean_ctor_set(x_81, 5, x_62);
lean_ctor_set(x_81, 6, x_80);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_2, x_72, x_75, x_83);
lean_dec(x_72);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_56);
return x_86;
}
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_TypeClass_newAnswer___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_back___at_Lean_TypeClass_consume___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_TypeClass_ConsumerNode_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_1);
return x_2;
}
}
lean_object* l_Stack_pop___at_Lean_TypeClass_consume___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_pop(x_1);
return x_2;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Queue_enqueue___rarg(x_9, x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* _init_l_Lean_TypeClass_consume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("answer ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_consume___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" not fully instantiated");
return x_1;
}
}
lean_object* l_Lean_TypeClass_consume(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_ctor_get(x_3, 4);
x_11 = lean_ctor_get(x_3, 5);
x_12 = lean_ctor_get(x_3, 6);
x_13 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_10);
x_14 = lean_array_pop(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set(x_3, 4, x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_17);
x_20 = l_Lean_TypeClass_Context_eInstantiate___main(x_17, x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_TypeClass_Context_eInstantiate___main(x_17, x_21);
lean_inc(x_22);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_20);
x_24 = l_Lean_TypeClass_Context_eHasTmpMVar(x_20);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_22);
x_25 = l_Lean_TypeClass_Context_eHasTmpMVar(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_20);
x_26 = lean_box(0);
lean_ctor_set(x_1, 0, x_26);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = l_Lean_TypeClass_newAnswer(x_27, x_23, x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_23);
lean_dec(x_16);
x_29 = lean_expr_dbg_to_string(x_20);
lean_dec(x_20);
x_30 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_expr_dbg_to_string(x_22);
lean_dec(x_22);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Option_HasRepr___rarg___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_TypeClass_consume___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_TypeClass_consume___closed__2;
x_41 = lean_string_append(x_39, x_40);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
lean_dec(x_16);
x_42 = lean_expr_dbg_to_string(x_20);
lean_dec(x_20);
x_43 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_List_reprAux___main___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_expr_dbg_to_string(x_22);
lean_dec(x_22);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l_Option_HasRepr___rarg___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lean_TypeClass_consume___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_TypeClass_consume___closed__2;
x_54 = lean_string_append(x_52, x_53);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_54);
return x_1;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_15, 0);
lean_inc(x_55);
lean_dec(x_15);
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_57);
x_58 = l_Lean_TypeClass_Context_eInfer(x_57, x_55);
lean_inc(x_57);
x_59 = l_Lean_TypeClass_Context_eInstantiate___main(x_57, x_58);
x_60 = l_Lean_TypeClass_Context__u03b1Norm(x_59);
lean_inc(x_13);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_13);
x_62 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_12, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_63 = lean_box(0);
lean_ctor_set(x_1, 0, x_63);
x_64 = l_Lean_TypeClass_newSubgoal(x_61, x_57, x_60, x_55, x_1);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_3);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4(x_13, x_65, x_67, x_68, x_11);
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_65, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
x_73 = lean_array_push(x_66, x_61);
lean_ctor_set(x_65, 0, x_73);
x_74 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_12, x_60, x_65);
x_75 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_75, 0, x_6);
lean_ctor_set(x_75, 1, x_7);
lean_ctor_set(x_75, 2, x_8);
lean_ctor_set(x_75, 3, x_9);
lean_ctor_set(x_75, 4, x_14);
lean_ctor_set(x_75, 5, x_69);
lean_ctor_set(x_75, 6, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_76);
return x_1;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_65);
x_77 = lean_array_push(x_66, x_61);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
x_79 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_12, x_60, x_78);
x_80 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_80, 0, x_6);
lean_ctor_set(x_80, 1, x_7);
lean_ctor_set(x_80, 2, x_8);
lean_ctor_set(x_80, 3, x_9);
lean_ctor_set(x_80, 4, x_14);
lean_ctor_set(x_80, 5, x_69);
lean_ctor_set(x_80, 6, x_79);
x_81 = lean_box(0);
lean_ctor_set(x_1, 1, x_80);
lean_ctor_set(x_1, 0, x_81);
return x_1;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_ctor_get(x_3, 0);
x_83 = lean_ctor_get(x_3, 1);
x_84 = lean_ctor_get(x_3, 2);
x_85 = lean_ctor_get(x_3, 3);
x_86 = lean_ctor_get(x_3, 4);
x_87 = lean_ctor_get(x_3, 5);
x_88 = lean_ctor_get(x_3, 6);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_3);
x_89 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_86);
x_90 = lean_array_pop(x_86);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_90);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
x_91 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_83);
lean_ctor_set(x_91, 2, x_84);
lean_ctor_set(x_91, 3, x_85);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set(x_91, 5, x_87);
lean_ctor_set(x_91, 6, x_88);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_inc(x_94);
x_97 = l_Lean_TypeClass_Context_eInstantiate___main(x_94, x_96);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l_Lean_TypeClass_Context_eInstantiate___main(x_94, x_98);
lean_inc(x_99);
lean_inc(x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_97);
x_101 = l_Lean_TypeClass_Context_eHasTmpMVar(x_97);
if (x_101 == 0)
{
uint8_t x_102; 
lean_inc(x_99);
x_102 = l_Lean_TypeClass_Context_eHasTmpMVar(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_99);
lean_dec(x_97);
x_103 = lean_box(0);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
x_104 = lean_ctor_get(x_93, 0);
lean_inc(x_104);
lean_dec(x_93);
x_105 = l_Lean_TypeClass_newAnswer(x_104, x_100, x_1);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_100);
lean_dec(x_93);
x_106 = lean_expr_dbg_to_string(x_97);
lean_dec(x_97);
x_107 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = l_List_reprAux___main___rarg___closed__1;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_expr_dbg_to_string(x_99);
lean_dec(x_99);
x_112 = lean_string_append(x_110, x_111);
lean_dec(x_111);
x_113 = l_Option_HasRepr___rarg___closed__3;
x_114 = lean_string_append(x_112, x_113);
x_115 = l_Lean_TypeClass_consume___closed__1;
x_116 = lean_string_append(x_115, x_114);
lean_dec(x_114);
x_117 = l_Lean_TypeClass_consume___closed__2;
x_118 = lean_string_append(x_116, x_117);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_118);
return x_1;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_100);
lean_dec(x_93);
x_119 = lean_expr_dbg_to_string(x_97);
lean_dec(x_97);
x_120 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l_List_reprAux___main___rarg___closed__1;
x_123 = lean_string_append(x_121, x_122);
x_124 = lean_expr_dbg_to_string(x_99);
lean_dec(x_99);
x_125 = lean_string_append(x_123, x_124);
lean_dec(x_124);
x_126 = l_Option_HasRepr___rarg___closed__3;
x_127 = lean_string_append(x_125, x_126);
x_128 = l_Lean_TypeClass_consume___closed__1;
x_129 = lean_string_append(x_128, x_127);
lean_dec(x_127);
x_130 = l_Lean_TypeClass_consume___closed__2;
x_131 = lean_string_append(x_129, x_130);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_131);
return x_1;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_92, 0);
lean_inc(x_132);
lean_dec(x_92);
x_133 = lean_ctor_get(x_89, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
lean_inc(x_134);
x_135 = l_Lean_TypeClass_Context_eInfer(x_134, x_132);
lean_inc(x_134);
x_136 = l_Lean_TypeClass_Context_eInstantiate___main(x_134, x_135);
x_137 = l_Lean_TypeClass_Context__u03b1Norm(x_136);
lean_inc(x_89);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_89);
x_139 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_88, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
x_140 = lean_box(0);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_140);
x_141 = l_Lean_TypeClass_newSubgoal(x_138, x_134, x_137, x_132, x_1);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_91);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4(x_89, x_142, x_144, x_145, x_87);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_array_push(x_143, x_138);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_144);
x_150 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_88, x_137, x_149);
x_151 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_151, 0, x_82);
lean_ctor_set(x_151, 1, x_83);
lean_ctor_set(x_151, 2, x_84);
lean_ctor_set(x_151, 3, x_85);
lean_ctor_set(x_151, 4, x_90);
lean_ctor_set(x_151, 5, x_146);
lean_ctor_set(x_151, 6, x_150);
x_152 = lean_box(0);
lean_ctor_set(x_1, 1, x_151);
lean_ctor_set(x_1, 0, x_152);
return x_1;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_153 = lean_ctor_get(x_1, 1);
lean_inc(x_153);
lean_dec(x_1);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 5);
lean_inc(x_159);
x_160 = lean_ctor_get(x_153, 6);
lean_inc(x_160);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 lean_ctor_release(x_153, 3);
 lean_ctor_release(x_153, 4);
 lean_ctor_release(x_153, 5);
 lean_ctor_release(x_153, 6);
 x_161 = x_153;
} else {
 lean_dec_ref(x_153);
 x_161 = lean_box(0);
}
x_162 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_158);
x_163 = lean_array_pop(x_158);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_163);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 7, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_154);
lean_ctor_set(x_164, 1, x_155);
lean_ctor_set(x_164, 2, x_156);
lean_ctor_set(x_164, 3, x_157);
lean_ctor_set(x_164, 4, x_163);
lean_ctor_set(x_164, 5, x_159);
lean_ctor_set(x_164, 6, x_160);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_inc(x_167);
x_170 = l_Lean_TypeClass_Context_eInstantiate___main(x_167, x_169);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = l_Lean_TypeClass_Context_eInstantiate___main(x_167, x_171);
lean_inc(x_172);
lean_inc(x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_170);
x_174 = l_Lean_TypeClass_Context_eHasTmpMVar(x_170);
if (x_174 == 0)
{
uint8_t x_175; 
lean_inc(x_172);
x_175 = l_Lean_TypeClass_Context_eHasTmpMVar(x_172);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_172);
lean_dec(x_170);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_164);
x_178 = lean_ctor_get(x_166, 0);
lean_inc(x_178);
lean_dec(x_166);
x_179 = l_Lean_TypeClass_newAnswer(x_178, x_173, x_177);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_173);
lean_dec(x_166);
x_180 = lean_expr_dbg_to_string(x_170);
lean_dec(x_170);
x_181 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
x_183 = l_List_reprAux___main___rarg___closed__1;
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_expr_dbg_to_string(x_172);
lean_dec(x_172);
x_186 = lean_string_append(x_184, x_185);
lean_dec(x_185);
x_187 = l_Option_HasRepr___rarg___closed__3;
x_188 = lean_string_append(x_186, x_187);
x_189 = l_Lean_TypeClass_consume___closed__1;
x_190 = lean_string_append(x_189, x_188);
lean_dec(x_188);
x_191 = l_Lean_TypeClass_consume___closed__2;
x_192 = lean_string_append(x_190, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_164);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_173);
lean_dec(x_166);
x_194 = lean_expr_dbg_to_string(x_170);
lean_dec(x_170);
x_195 = l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
x_196 = lean_string_append(x_195, x_194);
lean_dec(x_194);
x_197 = l_List_reprAux___main___rarg___closed__1;
x_198 = lean_string_append(x_196, x_197);
x_199 = lean_expr_dbg_to_string(x_172);
lean_dec(x_172);
x_200 = lean_string_append(x_198, x_199);
lean_dec(x_199);
x_201 = l_Option_HasRepr___rarg___closed__3;
x_202 = lean_string_append(x_200, x_201);
x_203 = l_Lean_TypeClass_consume___closed__1;
x_204 = lean_string_append(x_203, x_202);
lean_dec(x_202);
x_205 = l_Lean_TypeClass_consume___closed__2;
x_206 = lean_string_append(x_204, x_205);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_164);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_165, 0);
lean_inc(x_208);
lean_dec(x_165);
x_209 = lean_ctor_get(x_162, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
lean_inc(x_210);
x_211 = l_Lean_TypeClass_Context_eInfer(x_210, x_208);
lean_inc(x_210);
x_212 = l_Lean_TypeClass_Context_eInstantiate___main(x_210, x_211);
x_213 = l_Lean_TypeClass_Context__u03b1Norm(x_212);
lean_inc(x_162);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_162);
x_215 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_160, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_164);
x_218 = l_Lean_TypeClass_newSubgoal(x_214, x_210, x_213, x_208, x_217);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_164);
x_219 = lean_ctor_get(x_215, 0);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
x_222 = lean_unsigned_to_nat(0u);
x_223 = l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4(x_162, x_219, x_221, x_222, x_159);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_224 = x_219;
} else {
 lean_dec_ref(x_219);
 x_224 = lean_box(0);
}
x_225 = lean_array_push(x_220, x_214);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_221);
x_227 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_160, x_213, x_226);
x_228 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_228, 0, x_154);
lean_ctor_set(x_228, 1, x_155);
lean_ctor_set(x_228, 2, x_156);
lean_ctor_set(x_228, 3, x_157);
lean_ctor_set(x_228, 4, x_163);
lean_ctor_set(x_228, 5, x_223);
lean_ctor_set(x_228, 6, x_227);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
}
}
lean_object* l_Array_back___at_Lean_TypeClass_consume___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_TypeClass_consume___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_List_foldl___main___at_Lean_TypeClass_constNameToTypedExpr___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_TypeClass_Context_uNewMeta(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_10);
lean_ctor_set(x_8, 0, x_2);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_1 = x_14;
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_TypeClass_Context_uNewMeta(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_17);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_1 = x_24;
x_2 = x_16;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_TypeClass_constNameToTypedExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instance ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_constNameToTypedExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" not found in env");
return x_1;
}
}
lean_object* l_Lean_TypeClass_constNameToTypedExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_environment_find(x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_9 = l_System_FilePath_dirName___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_2);
x_11 = l_Lean_TypeClass_constNameToTypedExpr___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_TypeClass_constNameToTypedExpr___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_18 = l_Lean_ConstantInfo_lparams(x_15);
x_19 = l_List_foldl___main___at_Lean_TypeClass_constNameToTypedExpr___spec__1(x_17, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_expr_mk_const(x_2, x_21);
x_23 = lean_instantiate_type_lparams(x_15, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_19, 0, x_24);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_25);
x_27 = lean_expr_mk_const(x_2, x_25);
x_28 = lean_instantiate_type_lparams(x_15, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_3, 0, x_30);
return x_3;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_inc(x_2);
x_33 = lean_environment_find(x_32, x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_2);
x_36 = l_Lean_TypeClass_constNameToTypedExpr___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_TypeClass_constNameToTypedExpr___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
x_44 = l_Lean_ConstantInfo_lparams(x_41);
x_45 = l_List_foldl___main___at_Lean_TypeClass_constNameToTypedExpr___spec__1(x_43, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
lean_inc(x_46);
x_49 = lean_expr_mk_const(x_2, x_46);
x_50 = lean_instantiate_type_lparams(x_41, x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_31);
return x_53;
}
}
}
}
lean_object* l_Array_back___at_Lean_TypeClass_generate___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_TypeClass_GeneratorNode_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_TypeClass_generate___spec__2(x_1);
return x_2;
}
}
lean_object* l_Stack_pop___at_Lean_TypeClass_generate___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_pop(x_1);
return x_2;
}
}
lean_object* l_Stack_modify___at_Lean_TypeClass_generate___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
x_6 = lean_nat_dec_lt(x_5, x_3);
lean_dec(x_3);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_1, x_5);
x_8 = l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1;
x_9 = lean_array_fset(x_1, x_5, x_8);
x_10 = lean_apply_1(x_2, x_7);
x_11 = lean_array_fset(x_9, x_5, x_10);
lean_dec(x_5);
return x_11;
}
}
}
lean_object* l_Lean_TypeClass_generate___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
}
}
lean_object* _init_l_Lean_TypeClass_generate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("local instances not yet supported");
return x_1;
}
}
lean_object* l_Lean_TypeClass_generate(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 6);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_TypeClass_generate___spec__2(x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 6);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 5);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
x_22 = lean_array_pop(x_8);
lean_ctor_set(x_3, 3, x_22);
x_23 = lean_box(0);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_24 = lean_array_pop(x_8);
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_9);
lean_ctor_set(x_25, 5, x_10);
lean_ctor_set(x_25, 6, x_11);
x_26 = lean_box(0);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
x_28 = l_Lean_TypeClass_generate___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
lean_ctor_set(x_1, 0, x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_TypeClass_constNameToTypedExpr(x_33, x_30, x_1);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_34, 0);
lean_ctor_set(x_34, 0, x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_32, 2);
lean_inc(x_39);
x_40 = l_Lean_TypeClass_tryResolve(x_38, x_39, x_37, x_34);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_42, 3);
x_46 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_46, 0, x_29);
x_47 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_45, x_46);
lean_ctor_set(x_42, 3, x_47);
if (lean_obj_tag(x_44) == 0)
{
lean_dec(x_32);
lean_ctor_set(x_40, 0, x_31);
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
lean_ctor_set(x_40, 0, x_31);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_TypeClass_newConsumerNode(x_32, x_49, x_50, x_40);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
x_55 = lean_ctor_get(x_42, 2);
x_56 = lean_ctor_get(x_42, 3);
x_57 = lean_ctor_get(x_42, 4);
x_58 = lean_ctor_get(x_42, 5);
x_59 = lean_ctor_get(x_42, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_60 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_60, 0, x_29);
x_61 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_56, x_60);
x_62 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_59);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_32);
lean_ctor_set(x_40, 1, x_62);
lean_ctor_set(x_40, 0, x_31);
return x_40;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
lean_ctor_set(x_40, 1, x_62);
lean_ctor_set(x_40, 0, x_31);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_TypeClass_newConsumerNode(x_32, x_64, x_65, x_40);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_40, 1);
x_68 = lean_ctor_get(x_40, 0);
lean_inc(x_67);
lean_inc(x_68);
lean_dec(x_40);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 6);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 lean_ctor_release(x_67, 5);
 lean_ctor_release(x_67, 6);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_77, 0, x_29);
x_78 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_72, x_77);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 7, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 4, x_73);
lean_ctor_set(x_79, 5, x_74);
lean_ctor_set(x_79, 6, x_75);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_80; 
lean_dec(x_32);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_31);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
lean_dec(x_68);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_31);
lean_ctor_set(x_82, 1, x_79);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l_Lean_TypeClass_newConsumerNode(x_32, x_83, x_84, x_82);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_86 = lean_ctor_get(x_34, 0);
x_87 = lean_ctor_get(x_34, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_34);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_31);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_ctor_get(x_32, 2);
lean_inc(x_91);
x_92 = l_Lean_TypeClass_tryResolve(x_90, x_91, x_89, x_88);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 5);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 lean_ctor_release(x_93, 5);
 lean_ctor_release(x_93, 6);
 x_103 = x_93;
} else {
 lean_dec_ref(x_93);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_104, 0, x_29);
x_105 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_99, x_104);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_97);
lean_ctor_set(x_106, 2, x_98);
lean_ctor_set(x_106, 3, x_105);
lean_ctor_set(x_106, 4, x_100);
lean_ctor_set(x_106, 5, x_101);
lean_ctor_set(x_106, 6, x_102);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_107; 
lean_dec(x_32);
if (lean_is_scalar(x_95)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_95;
}
lean_ctor_set(x_107, 0, x_31);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_94, 0);
lean_inc(x_108);
lean_dec(x_94);
if (lean_is_scalar(x_95)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_95;
}
lean_ctor_set(x_109, 0, x_31);
lean_ctor_set(x_109, 1, x_106);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = l_Lean_TypeClass_newConsumerNode(x_32, x_110, x_111, x_109);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_32);
lean_dec(x_29);
x_113 = !lean_is_exclusive(x_34);
if (x_113 == 0)
{
return x_34;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_34, 0);
x_115 = lean_ctor_get(x_34, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_34);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_1, 1);
lean_inc(x_117);
lean_dec(x_1);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 5);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 6);
lean_inc(x_124);
x_125 = l_Array_back___at_Lean_TypeClass_generate___spec__2(x_121);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 lean_ctor_release(x_117, 6);
 x_127 = x_117;
} else {
 lean_dec_ref(x_117);
 x_127 = lean_box(0);
}
x_128 = lean_array_pop(x_121);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 7, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_119);
lean_ctor_set(x_129, 2, x_120);
lean_ctor_set(x_129, 3, x_128);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
lean_ctor_set(x_129, 6, x_124);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_132);
lean_dec(x_126);
lean_dec(x_125);
x_133 = l_Lean_TypeClass_generate___closed__1;
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_117);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
lean_dec(x_126);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
lean_dec(x_132);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_117);
x_139 = lean_ctor_get(x_125, 0);
lean_inc(x_139);
lean_dec(x_125);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
x_141 = l_Lean_TypeClass_constNameToTypedExpr(x_140, x_136, x_138);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_ctor_get(x_139, 2);
lean_inc(x_148);
x_149 = l_Lean_TypeClass_tryResolve(x_147, x_148, x_146, x_145);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_150, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 4);
lean_inc(x_157);
x_158 = lean_ctor_get(x_150, 5);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 6);
lean_inc(x_159);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 lean_ctor_release(x_150, 4);
 lean_ctor_release(x_150, 5);
 lean_ctor_release(x_150, 6);
 x_160 = x_150;
} else {
 lean_dec_ref(x_150);
 x_160 = lean_box(0);
}
x_161 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_161, 0, x_135);
x_162 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_156, x_161);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(0, 7, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_154);
lean_ctor_set(x_163, 2, x_155);
lean_ctor_set(x_163, 3, x_162);
lean_ctor_set(x_163, 4, x_157);
lean_ctor_set(x_163, 5, x_158);
lean_ctor_set(x_163, 6, x_159);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_164; 
lean_dec(x_139);
if (lean_is_scalar(x_152)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_152;
}
lean_ctor_set(x_164, 0, x_137);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_151, 0);
lean_inc(x_165);
lean_dec(x_151);
if (lean_is_scalar(x_152)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_152;
}
lean_ctor_set(x_166, 0, x_137);
lean_ctor_set(x_166, 1, x_163);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = l_Lean_TypeClass_newConsumerNode(x_139, x_167, x_168, x_166);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_139);
lean_dec(x_135);
x_170 = lean_ctor_get(x_141, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_141, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_172 = x_141;
} else {
 lean_dec_ref(x_141);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
}
}
lean_object* l_Array_back___at_Lean_TypeClass_generate___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_TypeClass_generate___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_TypeClass_step___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("FAILED TO SYNTHESIZE");
return x_1;
}
}
lean_object* l_Lean_TypeClass_step(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = lean_box(0);
lean_inc(x_3);
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_7 = l_Queue_isEmpty___rarg(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = l_Lean_TypeClass_resume(x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = l_Array_isEmpty___rarg(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = l_Lean_TypeClass_consume(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = l_Array_isEmpty___rarg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = l_Lean_TypeClass_generate(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_TypeClass_step___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_box(0);
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_ctor_get(x_17, 5);
lean_inc(x_20);
x_21 = l_Queue_isEmpty___rarg(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = l_Lean_TypeClass_resume(x_19);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_17, 4);
lean_inc(x_23);
x_24 = l_Array_isEmpty___rarg(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_17);
x_25 = l_Lean_TypeClass_consume(x_19);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_17, 3);
lean_inc(x_26);
x_27 = l_Array_isEmpty___rarg(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_17);
x_28 = l_Lean_TypeClass_generate(x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
x_29 = l_Lean_TypeClass_step___closed__1;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_17);
return x_30;
}
}
}
}
}
}
lean_object* _init_l_Lean_TypeClass_synthCore___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[synthCore] out of fuel");
return x_1;
}
}
lean_object* l_Lean_TypeClass_synthCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_TypeClass_step(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_1 = x_6;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 0);
lean_dec(x_27);
x_28 = l_Lean_TypeClass_synthCore___main___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Lean_TypeClass_synthCore___main___closed__1;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
lean_object* l_Lean_TypeClass_synthCore___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_synthCore___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeClass_synthCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_TypeClass_synthCore___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_TypeClass_synthCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeClass_synthCore(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TypeClass_collectUReplacements___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Level_hasMVar___main(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_array_push(x_4, x_7);
x_1 = x_8;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_TypeClass_Context_uNewMeta(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_ctor_set(x_12, 1, x_7);
x_16 = lean_array_push(x_3, x_12);
x_17 = lean_array_push(x_4, x_14);
x_1 = x_8;
x_2 = x_15;
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_array_push(x_3, x_21);
x_23 = lean_array_push(x_4, x_19);
x_1 = x_8;
x_2 = x_20;
x_3 = x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
lean_object* l_Lean_TypeClass_collectUReplacements(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_TypeClass_collectUReplacements___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TypeClass_Context_Inhabited;
x_2 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__2;
x_19 = lean_panic_fn(x_17);
return x_19;
}
}
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.TypeClass.Synth");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TODO(dselsam): this case not yet handled");
return x_1;
}
}
lean_object* l_Lean_TypeClass_collectEReplacements___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_10);
x_14 = lean_is_out_param(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_inc(x_12);
x_15 = lean_expr_instantiate1(x_11, x_12);
x_16 = lean_array_push(x_7, x_12);
x_3 = x_15;
x_4 = x_13;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_LocalContext_mkForall(x_1, x_2, x_10);
x_19 = l_Lean_TypeClass_Context_eNewMeta(x_18, x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_21);
x_24 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_2, x_2, x_23, x_21);
lean_inc(x_24);
x_25 = lean_expr_instantiate1(x_11, x_24);
lean_ctor_set(x_19, 1, x_12);
x_26 = lean_array_push(x_6, x_19);
x_27 = lean_array_push(x_7, x_24);
x_3 = x_25;
x_4 = x_13;
x_5 = x_22;
x_6 = x_26;
x_7 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_29);
x_32 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_2, x_2, x_31, x_29);
lean_inc(x_32);
x_33 = lean_expr_instantiate1(x_11, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_12);
x_35 = lean_array_push(x_6, x_34);
x_36 = lean_array_push(x_7, x_32);
x_3 = x_33;
x_4 = x_13;
x_5 = x_30;
x_6 = x_35;
x_7 = x_36;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_41 = lean_unsigned_to_nat(268u);
x_42 = lean_unsigned_to_nat(27u);
x_43 = l_Lean_TypeClass_collectEReplacements___main___closed__2;
x_44 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1(x_40, x_41, x_42, x_43);
return x_44;
}
}
}
}
lean_object* l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_TypeClass_collectEReplacements___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_TypeClass_collectEReplacements___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_TypeClass_collectEReplacements(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TypeClass_collectEReplacements___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_TypeClass_collectEReplacements___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_collectEReplacements(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_TypeClass_preprocessForOutParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("found constant not in the environment");
return x_1;
}
}
lean_object* l_Lean_TypeClass_preprocessForOutParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_279; 
x_279 = lean_expr_has_mvar(x_2);
if (x_279 == 0)
{
lean_object* x_280; uint8_t x_281; 
x_280 = l_Lean_Expr_getAppFn___main(x_2);
x_281 = l_Lean_Expr_isConst(x_280);
if (x_281 == 0)
{
lean_object* x_282; 
lean_dec(x_280);
x_282 = lean_box(0);
x_3 = x_282;
goto block_278;
}
else
{
lean_object* x_283; uint8_t x_284; 
x_283 = l_Lean_Expr_constName(x_280);
lean_dec(x_280);
lean_inc(x_1);
x_284 = lean_has_out_params(x_1, x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_1);
x_285 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_2);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
else
{
lean_object* x_289; 
x_289 = lean_box(0);
x_3 = x_289;
goto block_278;
}
}
}
else
{
lean_object* x_290; 
x_290 = lean_box(0);
x_3 = x_290;
goto block_278;
}
block_278:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_LocalContext_Inhabited___closed__1;
x_6 = l_Array_empty___closed__1;
lean_inc(x_2);
x_7 = l_Lean_TypeClass_introduceLocals___main(x_4, x_5, x_6, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Expr_getAppFn___main(x_2);
x_15 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_4);
x_16 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
lean_inc(x_2);
x_20 = l___private_Init_Lean_Expr_1__getAppArgsAux___main(x_2, x_17, x_19);
x_21 = l_Lean_Expr_isConst(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_22 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
lean_ctor_set(x_9, 1, x_22);
lean_ctor_set(x_9, 0, x_2);
x_23 = l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_constName(x_14);
lean_inc(x_24);
lean_inc(x_1);
x_25 = lean_is_class(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_26 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
lean_ctor_set(x_9, 1, x_26);
lean_ctor_set(x_9, 0, x_2);
x_27 = l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_free_object(x_9);
lean_free_object(x_7);
lean_dec(x_2);
x_28 = l_Lean_Expr_constLevels(x_14);
x_29 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_30 = l_Lean_TypeClass_collectUReplacements___main(x_28, x_29, x_6, x_6);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = l_Array_isEmpty___rarg(x_33);
x_37 = l_Array_toList___rarg(x_20);
lean_dec(x_20);
if (x_36 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_14);
x_38 = l_Array_toList___rarg(x_34);
lean_dec(x_34);
lean_inc(x_38);
x_39 = lean_expr_mk_const(x_24, x_38);
x_40 = l_Lean_Expr_constName(x_39);
x_41 = lean_environment_find(x_1, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_38);
x_70 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_71 = lean_unsigned_to_nat(284u);
x_72 = lean_unsigned_to_nat(16u);
x_73 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_74 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_70, x_71, x_72, x_73);
lean_inc(x_12);
lean_inc(x_11);
x_75 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_12, x_74, x_37, x_32, x_6, x_6);
x_42 = x_75;
goto block_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_instantiate_type_lparams(x_76, x_38);
lean_inc(x_12);
lean_inc(x_11);
x_78 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_12, x_77, x_37, x_32, x_6, x_6);
x_42 = x_78;
goto block_69;
}
block_69:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 1);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
x_49 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_48, x_48, x_4, x_39);
lean_dec(x_48);
x_50 = l_Lean_LocalContext_mkForall(x_11, x_12, x_49);
lean_ctor_set(x_44, 1, x_47);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_42, 0, x_50);
if (lean_is_scalar(x_35)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_35;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_54, x_54, x_4, x_39);
lean_dec(x_54);
x_56 = l_Lean_LocalContext_mkForall(x_11, x_12, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_42, 1, x_57);
lean_ctor_set(x_42, 0, x_56);
if (lean_is_scalar(x_35)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_35;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_42);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_42, 1);
x_60 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_62, x_62, x_4, x_39);
lean_dec(x_62);
x_65 = l_Lean_LocalContext_mkForall(x_11, x_12, x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_33);
lean_ctor_set(x_66, 1, x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_35)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_35;
}
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_environment_find(x_1, x_24);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_34);
x_108 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_109 = lean_unsigned_to_nat(284u);
x_110 = lean_unsigned_to_nat(16u);
x_111 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_112 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_108, x_109, x_110, x_111);
lean_inc(x_12);
lean_inc(x_11);
x_113 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_12, x_112, x_37, x_32, x_6, x_6);
x_80 = x_113;
goto block_107;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_79, 0);
lean_inc(x_114);
lean_dec(x_79);
x_115 = l_Array_toList___rarg(x_34);
lean_dec(x_34);
x_116 = lean_instantiate_type_lparams(x_114, x_115);
lean_inc(x_12);
lean_inc(x_11);
x_117 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_12, x_116, x_37, x_32, x_6, x_6);
x_80 = x_117;
goto block_107;
}
block_107:
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_80, 1);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_80, 0);
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
x_87 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_86, x_86, x_4, x_14);
lean_dec(x_86);
x_88 = l_Lean_LocalContext_mkForall(x_11, x_12, x_87);
lean_ctor_set(x_82, 1, x_85);
lean_ctor_set(x_82, 0, x_33);
lean_ctor_set(x_80, 0, x_88);
if (lean_is_scalar(x_35)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_35;
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_80);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_93 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_92, x_92, x_4, x_14);
lean_dec(x_92);
x_94 = l_Lean_LocalContext_mkForall(x_11, x_12, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_33);
lean_ctor_set(x_95, 1, x_91);
lean_ctor_set(x_80, 1, x_95);
lean_ctor_set(x_80, 0, x_94);
if (lean_is_scalar(x_35)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_35;
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_80);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_80, 1);
x_98 = lean_ctor_get(x_80, 0);
lean_inc(x_97);
lean_inc(x_98);
lean_dec(x_80);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_100, x_100, x_4, x_14);
lean_dec(x_100);
x_103 = l_Lean_LocalContext_mkForall(x_11, x_12, x_102);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_33);
lean_ctor_set(x_104, 1, x_99);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_35)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_35;
}
lean_ctor_set(x_106, 0, x_98);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_118 = lean_ctor_get(x_7, 0);
x_119 = lean_ctor_get(x_9, 1);
lean_inc(x_119);
lean_dec(x_9);
x_120 = l_Lean_Expr_getAppFn___main(x_2);
x_121 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_4);
x_122 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_121);
x_123 = lean_mk_array(x_121, x_122);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_sub(x_121, x_124);
lean_dec(x_121);
lean_inc(x_2);
x_126 = l___private_Init_Lean_Expr_1__getAppArgsAux___main(x_2, x_123, x_125);
x_127 = l_Lean_Expr_isConst(x_120);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_1);
x_128 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_2);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_ctor_set(x_7, 1, x_129);
lean_ctor_set(x_7, 0, x_130);
return x_7;
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Expr_constName(x_120);
lean_inc(x_131);
lean_inc(x_1);
x_132 = lean_is_class(x_1, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_1);
x_133 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_2);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_TypeClass_Context_Inhabited___closed__1;
lean_ctor_set(x_7, 1, x_134);
lean_ctor_set(x_7, 0, x_135);
return x_7;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
lean_free_object(x_7);
lean_dec(x_2);
x_136 = l_Lean_Expr_constLevels(x_120);
x_137 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_138 = l_Lean_TypeClass_collectUReplacements___main(x_136, x_137, x_6, x_6);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_143 = x_139;
} else {
 lean_dec_ref(x_139);
 x_143 = lean_box(0);
}
x_144 = l_Array_isEmpty___rarg(x_141);
x_145 = l_Array_toList___rarg(x_126);
lean_dec(x_126);
if (x_144 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_120);
x_146 = l_Array_toList___rarg(x_142);
lean_dec(x_142);
lean_inc(x_146);
x_147 = lean_expr_mk_const(x_131, x_146);
x_148 = l_Lean_Expr_constName(x_147);
x_149 = lean_environment_find(x_1, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_146);
x_163 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_164 = lean_unsigned_to_nat(284u);
x_165 = lean_unsigned_to_nat(16u);
x_166 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_167 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_163, x_164, x_165, x_166);
lean_inc(x_119);
lean_inc(x_118);
x_168 = l_Lean_TypeClass_collectEReplacements___main(x_118, x_119, x_167, x_145, x_140, x_6, x_6);
x_150 = x_168;
goto block_162;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_149, 0);
lean_inc(x_169);
lean_dec(x_149);
x_170 = lean_instantiate_type_lparams(x_169, x_146);
lean_inc(x_119);
lean_inc(x_118);
x_171 = l_Lean_TypeClass_collectEReplacements___main(x_118, x_119, x_170, x_145, x_140, x_6, x_6);
x_150 = x_171;
goto block_162;
}
block_162:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
x_157 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_155, x_155, x_4, x_147);
lean_dec(x_155);
x_158 = l_Lean_LocalContext_mkForall(x_118, x_119, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_141);
lean_ctor_set(x_159, 1, x_154);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_143)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_143;
}
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_environment_find(x_1, x_131);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_142);
x_186 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_187 = lean_unsigned_to_nat(284u);
x_188 = lean_unsigned_to_nat(16u);
x_189 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_190 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_186, x_187, x_188, x_189);
lean_inc(x_119);
lean_inc(x_118);
x_191 = l_Lean_TypeClass_collectEReplacements___main(x_118, x_119, x_190, x_145, x_140, x_6, x_6);
x_173 = x_191;
goto block_185;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_172, 0);
lean_inc(x_192);
lean_dec(x_172);
x_193 = l_Array_toList___rarg(x_142);
lean_dec(x_142);
x_194 = lean_instantiate_type_lparams(x_192, x_193);
lean_inc(x_119);
lean_inc(x_118);
x_195 = l_Lean_TypeClass_collectEReplacements___main(x_118, x_119, x_194, x_145, x_140, x_6, x_6);
x_173 = x_195;
goto block_185;
}
block_185:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_174, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
x_180 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_178, x_178, x_4, x_120);
lean_dec(x_178);
x_181 = l_Lean_LocalContext_mkForall(x_118, x_119, x_180);
if (lean_is_scalar(x_179)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_179;
}
lean_ctor_set(x_182, 0, x_141);
lean_ctor_set(x_182, 1, x_177);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_143)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_143;
}
lean_ctor_set(x_184, 0, x_175);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_196 = lean_ctor_get(x_7, 1);
x_197 = lean_ctor_get(x_7, 0);
lean_inc(x_196);
lean_inc(x_197);
lean_dec(x_7);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = l_Lean_Expr_getAppFn___main(x_2);
x_201 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_4);
x_202 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_201);
x_203 = lean_mk_array(x_201, x_202);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_sub(x_201, x_204);
lean_dec(x_201);
lean_inc(x_2);
x_206 = l___private_Init_Lean_Expr_1__getAppArgsAux___main(x_2, x_203, x_205);
x_207 = l_Lean_Expr_isConst(x_200);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_206);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_208 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
if (lean_is_scalar(x_199)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_199;
}
lean_ctor_set(x_209, 0, x_2);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
else
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Expr_constName(x_200);
lean_inc(x_212);
lean_inc(x_1);
x_213 = lean_is_class(x_1, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_214 = l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1;
if (lean_is_scalar(x_199)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_199;
}
lean_ctor_set(x_215, 0, x_2);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
lean_dec(x_199);
lean_dec(x_2);
x_218 = l_Lean_Expr_constLevels(x_200);
x_219 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_220 = l_Lean_TypeClass_collectUReplacements___main(x_218, x_219, x_6, x_6);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
x_226 = l_Array_isEmpty___rarg(x_223);
x_227 = l_Array_toList___rarg(x_206);
lean_dec(x_206);
if (x_226 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_200);
x_228 = l_Array_toList___rarg(x_224);
lean_dec(x_224);
lean_inc(x_228);
x_229 = lean_expr_mk_const(x_212, x_228);
x_230 = l_Lean_Expr_constName(x_229);
x_231 = lean_environment_find(x_1, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_228);
x_245 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_246 = lean_unsigned_to_nat(284u);
x_247 = lean_unsigned_to_nat(16u);
x_248 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_249 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_245, x_246, x_247, x_248);
lean_inc(x_198);
lean_inc(x_197);
x_250 = l_Lean_TypeClass_collectEReplacements___main(x_197, x_198, x_249, x_227, x_222, x_6, x_6);
x_232 = x_250;
goto block_244;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_231, 0);
lean_inc(x_251);
lean_dec(x_231);
x_252 = lean_instantiate_type_lparams(x_251, x_228);
lean_inc(x_198);
lean_inc(x_197);
x_253 = l_Lean_TypeClass_collectEReplacements___main(x_197, x_198, x_252, x_227, x_222, x_6, x_6);
x_232 = x_253;
goto block_244;
}
block_244:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
x_239 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_237, x_237, x_4, x_229);
lean_dec(x_237);
x_240 = l_Lean_LocalContext_mkForall(x_197, x_198, x_239);
if (lean_is_scalar(x_238)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_238;
}
lean_ctor_set(x_241, 0, x_223);
lean_ctor_set(x_241, 1, x_236);
if (lean_is_scalar(x_235)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_235;
}
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
if (lean_is_scalar(x_225)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_225;
}
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_environment_find(x_1, x_212);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_224);
x_268 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_269 = lean_unsigned_to_nat(284u);
x_270 = lean_unsigned_to_nat(16u);
x_271 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_272 = l_panicWithPos___at_Lean_TypeClass_Context_eInfer___spec__1(x_268, x_269, x_270, x_271);
lean_inc(x_198);
lean_inc(x_197);
x_273 = l_Lean_TypeClass_collectEReplacements___main(x_197, x_198, x_272, x_227, x_222, x_6, x_6);
x_255 = x_273;
goto block_267;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_254, 0);
lean_inc(x_274);
lean_dec(x_254);
x_275 = l_Array_toList___rarg(x_224);
lean_dec(x_224);
x_276 = lean_instantiate_type_lparams(x_274, x_275);
lean_inc(x_198);
lean_inc(x_197);
x_277 = l_Lean_TypeClass_collectEReplacements___main(x_197, x_198, x_276, x_227, x_222, x_6, x_6);
x_255 = x_277;
goto block_267;
}
block_267:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_261 = x_256;
} else {
 lean_dec_ref(x_256);
 x_261 = lean_box(0);
}
x_262 = l_Array_miterateAux___main___at_Lean_mkApp___spec__1(x_260, x_260, x_4, x_200);
lean_dec(x_260);
x_263 = l_Lean_LocalContext_mkForall(x_197, x_198, x_262);
if (lean_is_scalar(x_261)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_261;
}
lean_ctor_set(x_264, 0, x_223);
lean_ctor_set(x_264, 1, x_259);
if (lean_is_scalar(x_258)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_258;
}
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
if (lean_is_scalar(x_225)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_225;
}
lean_ctor_set(x_266, 0, x_257);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_TypeClass_synth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthesized instance has mvar");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_synth___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("outParams do not match: ");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_synth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ≠ ");
return x_1;
}
}
lean_object* l_Lean_TypeClass_synth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
lean_inc(x_1);
x_9 = l_Lean_TypeClass_preprocessForOutParams(x_7, x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_Lean_TypeClass_Context_eNewMeta(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_TypeClass_Context__u03b1Norm(x_12);
x_17 = lean_box(1);
lean_inc(x_14);
lean_inc(x_15);
x_18 = l_Lean_TypeClass_newSubgoal(x_17, x_15, x_16, x_14, x_3);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 2);
lean_dec(x_23);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_18, 0, x_8);
x_24 = l_Lean_TypeClass_synthCore___main(x_2, x_18);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 0, x_8);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_29, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_29);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = l_Lean_TypeClass_Context_eInstantiate___main(x_32, x_28);
lean_inc(x_34);
x_35 = l_Lean_TypeClass_Context_eHasTmpMVar(x_34);
if (x_35 == 0)
{
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_36; 
lean_dec(x_34);
x_36 = l_Lean_TypeClass_synth___closed__1;
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Lean_TypeClass_Context_eInstantiate___main(x_37, x_28);
lean_inc(x_38);
x_39 = l_Lean_TypeClass_Context_eHasTmpMVar(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_27);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
x_41 = l_Lean_TypeClass_synth___closed__1;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_28);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_30, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_30, 0);
lean_dec(x_45);
x_46 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_47 = l_Lean_TypeClass_synth___closed__2;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_TypeClass_synth___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_expr_dbg_to_string(x_29);
lean_dec(x_29);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 0, x_52);
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_30);
x_53 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_54 = l_Lean_TypeClass_synth___closed__2;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = l_Lean_TypeClass_synth___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_expr_dbg_to_string(x_29);
lean_dec(x_29);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_27);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_24, 0);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_24);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_8);
lean_ctor_set(x_65, 1, x_15);
lean_inc(x_64);
lean_inc(x_1);
x_66 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_64, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_64);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = l_Lean_TypeClass_Context_eInstantiate___main(x_67, x_63);
lean_inc(x_69);
x_70 = l_Lean_TypeClass_Context_eHasTmpMVar(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
x_72 = l_Lean_TypeClass_synth___closed__1;
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_68;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_63);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
x_75 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_76 = l_Lean_TypeClass_synth___closed__2;
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
x_78 = l_Lean_TypeClass_synth___closed__3;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_expr_dbg_to_string(x_64);
lean_dec(x_64);
x_81 = lean_string_append(x_79, x_80);
lean_dec(x_80);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_74;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_15);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_24);
if (x_83 == 0)
{
return x_24;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_24, 0);
x_85 = lean_ctor_get(x_24, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_24);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_20, 0);
x_88 = lean_ctor_get(x_20, 1);
x_89 = lean_ctor_get(x_20, 3);
x_90 = lean_ctor_get(x_20, 4);
x_91 = lean_ctor_get(x_20, 5);
x_92 = lean_ctor_get(x_20, 6);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_20);
x_93 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_14);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set(x_93, 4, x_90);
lean_ctor_set(x_93, 5, x_91);
lean_ctor_set(x_93, 6, x_92);
lean_ctor_set(x_18, 1, x_93);
lean_ctor_set(x_18, 0, x_8);
x_94 = l_Lean_TypeClass_synthCore___main(x_2, x_18);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_8);
lean_ctor_set(x_100, 1, x_15);
lean_inc(x_99);
lean_inc(x_1);
x_101 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_99, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_99);
lean_dec(x_1);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = l_Lean_TypeClass_Context_eInstantiate___main(x_102, x_98);
lean_inc(x_104);
x_105 = l_Lean_TypeClass_Context_eHasTmpMVar(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_96);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_104);
x_107 = l_Lean_TypeClass_synth___closed__1;
if (lean_is_scalar(x_103)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_103;
 lean_ctor_set_tag(x_108, 1);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_96);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_98);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
x_110 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_111 = l_Lean_TypeClass_synth___closed__2;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lean_TypeClass_synth___closed__3;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_expr_dbg_to_string(x_99);
lean_dec(x_99);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
if (lean_is_scalar(x_109)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_109;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_96);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_15);
lean_dec(x_1);
x_118 = lean_ctor_get(x_94, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_94, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_120 = x_94;
} else {
 lean_dec_ref(x_94);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_18, 1);
lean_inc(x_122);
lean_dec(x_18);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 5);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 6);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 lean_ctor_release(x_122, 6);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 7, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_123);
lean_ctor_set(x_130, 1, x_124);
lean_ctor_set(x_130, 2, x_14);
lean_ctor_set(x_130, 3, x_125);
lean_ctor_set(x_130, 4, x_126);
lean_ctor_set(x_130, 5, x_127);
lean_ctor_set(x_130, 6, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_8);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_TypeClass_synthCore___main(x_2, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_8);
lean_ctor_set(x_138, 1, x_15);
lean_inc(x_137);
lean_inc(x_1);
x_139 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_137, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_137);
lean_dec(x_1);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
x_142 = l_Lean_TypeClass_Context_eInstantiate___main(x_140, x_136);
lean_inc(x_142);
x_143 = l_Lean_TypeClass_Context_eHasTmpMVar(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_141;
}
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_134);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_142);
x_145 = l_Lean_TypeClass_synth___closed__1;
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_141;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_134);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_136);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_147 = x_139;
} else {
 lean_dec_ref(x_139);
 x_147 = lean_box(0);
}
x_148 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_149 = l_Lean_TypeClass_synth___closed__2;
x_150 = lean_string_append(x_149, x_148);
lean_dec(x_148);
x_151 = l_Lean_TypeClass_synth___closed__3;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_expr_dbg_to_string(x_137);
lean_dec(x_137);
x_154 = lean_string_append(x_152, x_153);
lean_dec(x_153);
if (lean_is_scalar(x_147)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_147;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_134);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_15);
lean_dec(x_1);
x_156 = lean_ctor_get(x_132, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_132, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_158 = x_132;
} else {
 lean_dec_ref(x_132);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_18);
if (x_160 == 0)
{
return x_18;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_18, 0);
x_162 = lean_ctor_get(x_18, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_18);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_164 = lean_ctor_get(x_3, 1);
lean_inc(x_164);
lean_dec(x_3);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
lean_inc(x_1);
x_168 = l_Lean_TypeClass_preprocessForOutParams(x_165, x_1);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_171);
x_172 = l_Lean_TypeClass_Context_eNewMeta(x_171, x_170);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_TypeClass_Context__u03b1Norm(x_171);
x_176 = lean_box(1);
lean_inc(x_173);
lean_inc(x_174);
x_177 = l_Lean_TypeClass_newSubgoal(x_176, x_174, x_175, x_173, x_167);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
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
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_178, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 4);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 5);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 6);
lean_inc(x_185);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 lean_ctor_release(x_178, 6);
 x_186 = x_178;
} else {
 lean_dec_ref(x_178);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 7, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_180);
lean_ctor_set(x_187, 1, x_181);
lean_ctor_set(x_187, 2, x_173);
lean_ctor_set(x_187, 3, x_182);
lean_ctor_set(x_187, 4, x_183);
lean_ctor_set(x_187, 5, x_184);
lean_ctor_set(x_187, 6, x_185);
if (lean_is_scalar(x_179)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_179;
}
lean_ctor_set(x_188, 0, x_166);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_TypeClass_synthCore___main(x_2, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_190, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec(x_190);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_192;
}
lean_ctor_set(x_195, 0, x_166);
lean_ctor_set(x_195, 1, x_174);
lean_inc(x_194);
lean_inc(x_1);
x_196 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_194, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_194);
lean_dec(x_1);
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
x_199 = l_Lean_TypeClass_Context_eInstantiate___main(x_197, x_193);
lean_inc(x_199);
x_200 = l_Lean_TypeClass_Context_eHasTmpMVar(x_199);
if (x_200 == 0)
{
lean_object* x_201; 
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_191);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_199);
x_202 = l_Lean_TypeClass_synth___closed__1;
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_198;
 lean_ctor_set_tag(x_203, 1);
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_191);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_193);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_204 = x_196;
} else {
 lean_dec_ref(x_196);
 x_204 = lean_box(0);
}
x_205 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_206 = l_Lean_TypeClass_synth___closed__2;
x_207 = lean_string_append(x_206, x_205);
lean_dec(x_205);
x_208 = l_Lean_TypeClass_synth___closed__3;
x_209 = lean_string_append(x_207, x_208);
x_210 = lean_expr_dbg_to_string(x_194);
lean_dec(x_194);
x_211 = lean_string_append(x_209, x_210);
lean_dec(x_210);
if (lean_is_scalar(x_204)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_204;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_191);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_174);
lean_dec(x_1);
x_213 = lean_ctor_get(x_189, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_189, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_215 = x_189;
} else {
 lean_dec_ref(x_189);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_177, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_177, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_219 = x_177;
} else {
 lean_dec_ref(x_177);
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
lean_object* initialize_Init_Lean_Expr(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Class(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
lean_object* initialize_Init_Lean_TypeClass_Context(lean_object*);
lean_object* initialize_Init_Data_PersistentHashMap_Default(lean_object*);
lean_object* initialize_Init_Data_Stack_Default(lean_object*);
lean_object* initialize_Init_Data_Queue_Default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeClass_Synth(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Class(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_TypeClass_Context(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_PersistentHashMap_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stack_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TypeClass_TypedExpr_HasToString___closed__1 = _init_l_Lean_TypeClass_TypedExpr_HasToString___closed__1();
lean_mark_persistent(l_Lean_TypeClass_TypedExpr_HasToString___closed__1);
l_Lean_TypeClass_TypedExpr_Inhabited___closed__1 = _init_l_Lean_TypeClass_TypedExpr_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TypeClass_TypedExpr_Inhabited___closed__1);
l_Lean_TypeClass_TypedExpr_Inhabited = _init_l_Lean_TypeClass_TypedExpr_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_TypedExpr_Inhabited);
l_Lean_TypeClass_Node_Inhabited___closed__1 = _init_l_Lean_TypeClass_Node_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Node_Inhabited___closed__1);
l_Lean_TypeClass_Node_Inhabited = _init_l_Lean_TypeClass_Node_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_Node_Inhabited);
l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1 = _init_l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1);
l_Lean_TypeClass_ConsumerNode_Inhabited = _init_l_Lean_TypeClass_ConsumerNode_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_ConsumerNode_Inhabited);
l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1 = _init_l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1);
l_Lean_TypeClass_GeneratorNode_Inhabited = _init_l_Lean_TypeClass_GeneratorNode_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_GeneratorNode_Inhabited);
l_Lean_TypeClass_quickIsClass___main___closed__1 = _init_l_Lean_TypeClass_quickIsClass___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_quickIsClass___main___closed__1);
l_Lean_TypeClass_newSubgoal___closed__1 = _init_l_Lean_TypeClass_newSubgoal___closed__1();
lean_mark_persistent(l_Lean_TypeClass_newSubgoal___closed__1);
l_Lean_TypeClass_newSubgoal___closed__2 = _init_l_Lean_TypeClass_newSubgoal___closed__2();
lean_mark_persistent(l_Lean_TypeClass_newSubgoal___closed__2);
l_Lean_TypeClass_newSubgoal___closed__3 = _init_l_Lean_TypeClass_newSubgoal___closed__3();
lean_mark_persistent(l_Lean_TypeClass_newSubgoal___closed__3);
l_Lean_TypeClass_introduceLocals___main___closed__1 = _init_l_Lean_TypeClass_introduceLocals___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_introduceLocals___main___closed__1);
l_Lean_TypeClass_introduceLocals___main___closed__2 = _init_l_Lean_TypeClass_introduceLocals___main___closed__2();
lean_mark_persistent(l_Lean_TypeClass_introduceLocals___main___closed__2);
l_Lean_TypeClass_resume___closed__1 = _init_l_Lean_TypeClass_resume___closed__1();
lean_mark_persistent(l_Lean_TypeClass_resume___closed__1);
l_Lean_TypeClass_resume___closed__2 = _init_l_Lean_TypeClass_resume___closed__2();
lean_mark_persistent(l_Lean_TypeClass_resume___closed__2);
l_Lean_TypeClass_newAnswer___closed__1 = _init_l_Lean_TypeClass_newAnswer___closed__1();
lean_mark_persistent(l_Lean_TypeClass_newAnswer___closed__1);
l_Lean_TypeClass_newAnswer___closed__2 = _init_l_Lean_TypeClass_newAnswer___closed__2();
lean_mark_persistent(l_Lean_TypeClass_newAnswer___closed__2);
l_Lean_TypeClass_consume___closed__1 = _init_l_Lean_TypeClass_consume___closed__1();
lean_mark_persistent(l_Lean_TypeClass_consume___closed__1);
l_Lean_TypeClass_consume___closed__2 = _init_l_Lean_TypeClass_consume___closed__2();
lean_mark_persistent(l_Lean_TypeClass_consume___closed__2);
l_Lean_TypeClass_constNameToTypedExpr___closed__1 = _init_l_Lean_TypeClass_constNameToTypedExpr___closed__1();
lean_mark_persistent(l_Lean_TypeClass_constNameToTypedExpr___closed__1);
l_Lean_TypeClass_constNameToTypedExpr___closed__2 = _init_l_Lean_TypeClass_constNameToTypedExpr___closed__2();
lean_mark_persistent(l_Lean_TypeClass_constNameToTypedExpr___closed__2);
l_Lean_TypeClass_generate___closed__1 = _init_l_Lean_TypeClass_generate___closed__1();
lean_mark_persistent(l_Lean_TypeClass_generate___closed__1);
l_Lean_TypeClass_step___closed__1 = _init_l_Lean_TypeClass_step___closed__1();
lean_mark_persistent(l_Lean_TypeClass_step___closed__1);
l_Lean_TypeClass_synthCore___main___closed__1 = _init_l_Lean_TypeClass_synthCore___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_synthCore___main___closed__1);
l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1 = _init_l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1();
lean_mark_persistent(l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__1);
l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__2 = _init_l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__2();
lean_mark_persistent(l_panicWithPos___at_Lean_TypeClass_collectEReplacements___main___spec__1___closed__2);
l_Lean_TypeClass_collectEReplacements___main___closed__1 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__1);
l_Lean_TypeClass_collectEReplacements___main___closed__2 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__2();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__2);
l_Lean_TypeClass_preprocessForOutParams___closed__1 = _init_l_Lean_TypeClass_preprocessForOutParams___closed__1();
lean_mark_persistent(l_Lean_TypeClass_preprocessForOutParams___closed__1);
l_Lean_TypeClass_synth___closed__1 = _init_l_Lean_TypeClass_synth___closed__1();
lean_mark_persistent(l_Lean_TypeClass_synth___closed__1);
l_Lean_TypeClass_synth___closed__2 = _init_l_Lean_TypeClass_synth___closed__2();
lean_mark_persistent(l_Lean_TypeClass_synth___closed__2);
l_Lean_TypeClass_synth___closed__3 = _init_l_Lean_TypeClass_synth___closed__3();
lean_mark_persistent(l_Lean_TypeClass_synth___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
