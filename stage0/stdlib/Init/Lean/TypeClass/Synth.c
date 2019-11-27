// Lean compiler output
// Module: Init.Lean.TypeClass.Synth
// Imports: Init.Lean.Expr Init.Lean.Environment Init.Lean.Class Init.Lean.MetavarContext Init.Lean.TypeClass.Context Init.Data.PersistentHashMap Init.Data.Stack Init.Data.Queue
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
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_TypeClass_Node_Inhabited;
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_Inhabited;
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_newSubgoal___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_HasToString(lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_HasToString___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_newSubgoal___spec__5(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Queue_enqueue___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_TypeClass_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_TypeClass_generate(lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__2;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectUReplacements___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_formatDataValue___closed__1;
lean_object* l_Lean_TypeClass_TypedExpr_HasToString___boxed(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Stack_modify___at_Lean_TypeClass_generate___spec__4(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal___closed__3;
lean_object* l_Lean_TypeClass_collectUReplacements(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eInstantiate___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_TypeClass_Waiter_isRoot___boxed(lean_object*);
extern lean_object* l_Lean_TypeClass_Context_Inhabited;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_TypeClass_introduceLocals___main___closed__2;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_TypeClass_Context_eInfer(lean_object*, lean_object*);
uint8_t l_Queue_isEmpty___rarg(lean_object*);
lean_object* lean_get_class_instances(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_step___closed__1;
lean_object* l_Lean_TypeClass_quickIsClass___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Array_back___at_Lean_TypeClass_generate___spec__2(lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___rarg___closed__1;
lean_object* l_Lean_TypeClass_synth___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newConsumerNode(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_internalize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synth___closed__1;
lean_object* l_Lean_TypeClass_synthCore___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Array_back___at_Lean_TypeClass_generate___spec__2___boxed(lean_object*);
lean_object* l_Lean_TypeClass_constNameToTypedExpr___closed__2;
lean_object* l_Lean_TypeClass_introduceMVars___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_wakeUp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_constNameToTypedExpr___closed__1;
lean_object* l_Lean_TypeClass_GeneratorNode_Inhabited;
lean_object* l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Node_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_quickIsClass___main___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_TypeClass_constNameToTypedExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synthCore___boxed(lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newAnswer___closed__2;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__3;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_TypeClass_synthCore___main___closed__1;
lean_object* l_Lean_TypeClass_quickIsClass(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__5;
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newAnswer___closed__1;
lean_object* l_Lean_TypeClass_Answer_Inhabited;
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_TypeClass_Answer_HasToString(lean_object*);
lean_object* l_Lean_TypeClass_Context_uNewMeta(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_TypeClass_constNameToTypedExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Stack_pop___at_Lean_TypeClass_consume___spec__3(lean_object*);
lean_object* l_Array_back___at_Lean_TypeClass_consume___spec__2___boxed(lean_object*);
lean_object* l_Lean_TypeClass_preprocessForOutParams___closed__2;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___boxed(lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_TypeClass_synthCore___main(lean_object*, lean_object*);
uint8_t l_Lean_TypeClass_Context_eHasTmpMVar(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TypeClass_introduceMVars___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_TypeClass_ConsumerNode_Inhabited;
lean_object* l_Lean_TypeClass_collectEReplacements(lean_object*);
lean_object* l_Queue_dequeue_x3f___rarg(lean_object*);
lean_object* l_Lean_TypeClass_introduceLocals___main___closed__1;
lean_object* l_Lean_TypeClass_preprocessForOutParams___closed__1;
lean_object* l_Stack_pop___at_Lean_TypeClass_generate___spec__3(lean_object*);
lean_object* l_Lean_TypeClass_resume(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_TypeClass_Waiter_isRoot(lean_object*);
lean_object* l_Lean_TypeClass_consume(lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_TypeClass_collectEReplacements___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_TypeClass_preprocessForOutParams(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_ConsumerNode_Inhabited___closed__1;
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eNewMeta(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_TypeClass_consume___spec__2(lean_object*);
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_TypedExpr_Inhabited___closed__1;
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_generate___spec__1___boxed(lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TypeClass_generate___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_TypeClass_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Answer_HasToString___closed__1;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_TypeClass_resume___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_resume___closed__2;
lean_object* l_Lean_TypeClass_introduceMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Context_eUnify___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main___closed__4;
uint8_t l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_generate___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Lean_TypeClass_Context__u03b1Norm(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_wakeUp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synth(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_introduceMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_TypeClass_introduceLocals(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(lean_object*);
lean_object* l_Lean_TypeClass_step(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_GeneratorNode_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_newAnswer(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1___boxed(lean_object*);
lean_object* l_Lean_TypeClass_collectEReplacements___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TypeClass_Context_Inhabited___closed__1;
uint8_t lean_has_out_params(lean_object*, lean_object*);
lean_object* l_Stack_peek_x21___at_Lean_TypeClass_consume___spec__1(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal___closed__1;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synthCore(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_Answer_HasToString___boxed(lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_synth___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_introduceLocals___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeClass_newSubgoal___closed__2;
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
x_1 = l_Lean_Expr_Inhabited___closed__1;
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
lean_object* _init_l_Lean_TypeClass_Answer_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Answer(");
return x_1;
}
}
lean_object* l_Lean_TypeClass_Answer_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_expr_dbg_to_string(x_3);
x_6 = l_Lean_TypeClass_Answer_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_expr_dbg_to_string(x_4);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_Option_HasRepr___rarg___closed__3;
x_13 = lean_string_append(x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_TypeClass_Answer_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeClass_Answer_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_TypeClass_Answer_Inhabited() {
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
x_1 = l_Lean_Expr_Inhabited___closed__1;
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
uint8_t l_Lean_TypeClass_Waiter_isRoot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Lean_TypeClass_Waiter_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_TypeClass_Waiter_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
x_4 = lean_is_class(x_1, x_3);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
case 5:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Expr_getAppFn___main(x_10);
lean_dec(x_10);
x_12 = l_Lean_Expr_isConst(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_isLambda(x_11);
lean_dec(x_11);
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Expr_constName_x21(x_11);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_22 = l_Lean_Expr_constName_x21(x_11);
lean_inc(x_22);
x_23 = lean_is_class(x_1, x_22);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
lean_dec(x_22);
x_26 = l_Lean_Expr_isLambda(x_11);
lean_dec(x_11);
x_27 = l_Bool_DecidableEq(x_26, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_TypeClass_quickIsClass___main___closed__1;
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
case 7:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_dec(x_2);
x_2 = x_32;
goto _start;
}
case 8:
{
lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
return x_34;
}
case 10:
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_2 = x_35;
goto _start;
}
case 11:
{
lean_object* x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
return x_37;
}
default: 
{
lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_TypeClass_quickIsClass___main___closed__1;
return x_38;
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
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = lean_array_fset(x_5, x_2, x_3);
x_30 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_newSubgoal___spec__5(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Expr_hash(x_9);
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
x_22 = 1;
x_23 = l_Bool_DecidableEq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
x_24 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_fset(x_17, x_12, x_25);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_27 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_expr_eqv(x_4, x_28);
x_31 = 1;
x_32 = l_Bool_DecidableEq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_PersistentHashMap_mkCollisionNode___rarg(x_28, x_29, x_4, x_5);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_array_fset(x_17, x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
x_37 = lean_array_fset(x_17, x_12, x_36);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = x_2 >> x_9;
x_41 = x_3 + x_8;
x_42 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_39, x_40, x_41, x_4, x_5);
lean_ctor_set(x_15, 0, x_42);
x_43 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_43);
return x_1;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = x_2 >> x_9;
x_46 = x_3 + x_8;
x_47 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_44, x_45, x_46, x_4, x_5);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
default: 
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_5);
x_51 = lean_array_fset(x_17, x_12, x_50);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
}
}
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = 1;
x_54 = 5;
x_55 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_56 = x_2 & x_55;
x_57 = lean_usize_to_nat(x_56);
x_58 = lean_array_get_size(x_52);
x_59 = lean_nat_dec_lt(x_57, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_52);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_array_fget(x_52, x_57);
x_62 = lean_box(2);
x_63 = lean_array_fset(x_52, x_57, x_62);
switch (lean_obj_tag(x_61)) {
case 0:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
x_67 = lean_expr_eqv(x_4, x_64);
x_68 = 1;
x_69 = l_Bool_DecidableEq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
x_70 = l_PersistentHashMap_mkCollisionNode___rarg(x_64, x_65, x_4, x_5);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_array_fset(x_63, x_57, x_71);
lean_dec(x_57);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_65);
lean_dec(x_64);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_66;
}
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_5);
x_75 = lean_array_fset(x_63, x_57, x_74);
lean_dec(x_57);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
case 1:
{
lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_61, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
x_79 = x_2 >> x_54;
x_80 = x_3 + x_53;
x_81 = l_PersistentHashMap_insertAux___main___at_Lean_TypeClass_newSubgoal___spec__3(x_77, x_79, x_80, x_4, x_5);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_array_fset(x_63, x_57, x_82);
lean_dec(x_57);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_5);
x_86 = lean_array_fset(x_63, x_57, x_85);
lean_dec(x_57);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; size_t x_98; uint8_t x_99; 
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_TypeClass_newSubgoal___spec__4(x_1, x_88, x_4, x_5);
x_98 = 7;
x_99 = x_98 <= x_3;
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_89);
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_nat_dec_lt(x_100, x_101);
lean_dec(x_100);
x_90 = x_102;
goto block_97;
}
else
{
uint8_t x_103; 
x_103 = 1;
x_90 = x_103;
goto block_97;
}
block_97:
{
uint8_t x_91; uint8_t x_92; 
x_91 = 1;
x_92 = l_Bool_DecidableEq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_96 = l_Array_iterateMAux___main___at_Lean_TypeClass_newSubgoal___spec__5(x_3, x_93, x_94, x_93, x_88, x_95);
lean_dec(x_94);
lean_dec(x_93);
return x_96;
}
else
{
return x_89;
}
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
x_7 = l_Lean_Expr_hash(x_2);
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
x_14 = l_Lean_Expr_hash(x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_6 = l_Lean_TypeClass_Context_eInfer(x_2, x_4);
lean_inc(x_2);
x_7 = l_Lean_TypeClass_Context_eInstantiate___main(x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
lean_inc(x_7);
lean_inc(x_8);
x_15 = l_Lean_TypeClass_quickIsClass___main(x_8, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_expr_dbg_to_string(x_7);
lean_dec(x_7);
x_17 = l_Lean_TypeClass_newSubgoal___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_TypeClass_newSubgoal___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_expr_dbg_to_string(x_7);
lean_dec(x_7);
x_24 = l_Lean_TypeClass_newSubgoal___closed__3;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_formatDataValue___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_30 = lean_ctor_get(x_5, 6);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 5);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_5, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec(x_22);
x_38 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_39 = l_Lean_TypeClass_Context_internalize(x_2, x_4, x_7, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_inc(x_3);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_8);
x_46 = lean_get_class_instances(x_8, x_37);
x_47 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_mkOptionalNode___rarg___closed__1;
x_50 = lean_array_push(x_49, x_1);
x_51 = l_Array_empty___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_11, x_48);
x_54 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_14, x_3, x_52);
lean_ctor_set(x_5, 6, x_54);
lean_ctor_set(x_5, 3, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_5);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_5);
x_57 = lean_ctor_get(x_22, 0);
lean_inc(x_57);
lean_dec(x_22);
x_58 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_59 = l_Lean_TypeClass_Context_internalize(x_2, x_4, x_7, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_inc(x_3);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
lean_inc(x_8);
x_66 = lean_get_class_instances(x_8, x_57);
x_67 = l_List_map___main___at_Lean_TypeClass_newSubgoal___spec__1(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_mkOptionalNode___rarg___closed__1;
x_70 = lean_array_push(x_69, x_1);
x_71 = l_Array_empty___closed__1;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_11, x_68);
x_74 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_14, x_3, x_72);
x_75 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_75, 0, x_8);
lean_ctor_set(x_75, 1, x_9);
lean_ctor_set(x_75, 2, x_10);
lean_ctor_set(x_75, 3, x_73);
lean_ctor_set(x_75, 4, x_12);
lean_ctor_set(x_75, 5, x_13);
lean_ctor_set(x_75, 6, x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_newSubgoal___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_TypeClass_newSubgoal___spec__5(x_7, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_12; lean_object* x_13; uint64_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_15 = (uint8_t)((x_14 << 24) >> 61);
lean_inc(x_1);
x_16 = l_Lean_LocalContext_mkForall(x_1, x_2, x_12);
lean_dec(x_12);
x_17 = l_Lean_TypeClass_Context_eNewMeta(x_16, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
x_21 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_20, x_18);
lean_inc(x_21);
x_22 = l_Lean_mkApp(x_4, x_21);
x_23 = lean_expr_instantiate1(x_13, x_21);
lean_dec(x_21);
lean_dec(x_13);
x_24 = l_Lean_BinderInfo_isInstImplicit(x_15);
x_25 = 1;
x_26 = l_Bool_DecidableEq(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_18);
x_3 = x_19;
x_4 = x_22;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_6);
x_3 = x_19;
x_4 = x_22;
x_5 = x_23;
x_6 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_box(0);
x_7 = x_30;
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
lean_object* l_Lean_TypeClass_introduceMVars___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_TypeClass_introduceMVars___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_TypeClass_introduceMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_TypeClass_introduceMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_9 = (uint8_t)((x_8 << 24) >> 61);
x_10 = l_Lean_TypeClass_introduceLocals___main___closed__2;
lean_inc(x_1);
x_11 = lean_name_mk_numeral(x_10, x_1);
lean_inc(x_11);
x_12 = lean_local_ctx_mk_local_decl(x_2, x_11, x_5, x_6, x_9);
x_13 = l_Lean_mkFVar(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
lean_inc(x_13);
x_16 = lean_array_push(x_3, x_13);
x_17 = lean_expr_instantiate1(x_7, x_13);
lean_dec(x_13);
lean_dec(x_7);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
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
x_10 = l_Lean_LocalContext_Inhabited___closed__2;
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
x_17 = lean_box(0);
lean_inc(x_14);
x_18 = l_Lean_TypeClass_introduceMVars___main(x_14, x_16, x_1, x_7, x_8, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_26 = l_Lean_LocalContext_mkLambda(x_14, x_16, x_22);
lean_dec(x_22);
lean_dec(x_16);
x_27 = l_Lean_TypeClass_Context_eUnify___main(x_15, x_24, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_TypeClass_Context_eUnify___main(x_5, x_26, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_ctor_set(x_20, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
lean_ctor_set(x_20, 0, x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_20);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_20);
lean_dec(x_25);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_25);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_27, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 0, x_46);
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = l_Lean_LocalContext_mkLambda(x_14, x_16, x_22);
lean_dec(x_22);
lean_dec(x_16);
x_52 = l_Lean_TypeClass_Context_eUnify___main(x_15, x_49, x_21);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_TypeClass_Context_eUnify___main(x_5, x_51, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_50);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_50);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
 lean_ctor_set_tag(x_62, 0);
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_63 = x_52;
} else {
 lean_dec_ref(x_52);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
return x_65;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_array_push(x_9, x_7);
lean_ctor_set(x_4, 4, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
x_18 = lean_ctor_get(x_4, 5);
x_19 = lean_ctor_get(x_4, 6);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_20 = lean_array_push(x_17, x_7);
x_21 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 6);
lean_inc(x_34);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 x_35 = x_4;
} else {
 lean_dec_ref(x_4);
 x_35 = lean_box(0);
}
x_36 = lean_array_push(x_32, x_27);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 7, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
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
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
x_3 = l_Queue_dequeue_x3f___rarg(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_TypeClass_resume___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_10 = l_Lean_TypeClass_resume___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_TypeClass_Context_internalize(x_18, x_20, x_21, x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_26);
x_27 = l_Lean_TypeClass_Context_eInfer(x_26, x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
x_30 = l_Lean_TypeClass_tryResolve(x_26, x_28, x_29, x_1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_32, 5);
lean_dec(x_35);
lean_ctor_set(x_32, 5, x_12);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_15);
x_36 = lean_box(0);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_30);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_List_append___rarg(x_39, x_15);
x_41 = l_Lean_TypeClass_newConsumerNode(x_16, x_38, x_40, x_32);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
x_45 = lean_ctor_get(x_32, 2);
x_46 = lean_ctor_get(x_32, 3);
x_47 = lean_ctor_get(x_32, 4);
x_48 = lean_ctor_get(x_32, 6);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set(x_49, 4, x_47);
lean_ctor_set(x_49, 5, x_12);
lean_ctor_set(x_49, 6, x_48);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_50; 
lean_dec(x_16);
lean_dec(x_15);
x_50 = lean_box(0);
lean_ctor_set(x_30, 1, x_49);
lean_ctor_set(x_30, 0, x_50);
return x_30;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_30);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_List_append___rarg(x_53, x_15);
x_55 = l_Lean_TypeClass_newConsumerNode(x_16, x_52, x_54, x_49);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_30, 1);
x_57 = lean_ctor_get(x_30, 0);
lean_inc(x_56);
lean_inc(x_57);
lean_dec(x_30);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 6);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 7, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
lean_ctor_set(x_65, 5, x_12);
lean_ctor_set(x_65, 6, x_63);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_16);
lean_dec(x_15);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_List_append___rarg(x_70, x_15);
x_72 = l_Lean_TypeClass_newConsumerNode(x_16, x_69, x_71, x_65);
return x_72;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_Queue_enqueue___rarg(x_7, x_6);
lean_ctor_set(x_3, 5, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_3, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_1);
x_20 = l_Queue_enqueue___rarg(x_19, x_17);
x_21 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_21, 6, x_18);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_3, 1, x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
x_34 = lean_ctor_get(x_3, 5);
x_35 = lean_ctor_get(x_3, 6);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 4, x_33);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Bool_DecidableEq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
}
case 1:
{
lean_object* x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = x_2 >> x_5;
x_20 = l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(x_18, x_19, x_3);
lean_dec(x_18);
return x_20;
}
default: 
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_PersistentHashMap_findAtAux___main___at_Lean_TypeClass_newAnswer___spec__3(x_22, x_23, lean_box(0), x_24, x_3);
return x_25;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_TypeClass_newAnswer___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_TypeClass_Context__u03b1Norm(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_TypeClass_Context__u03b1Norm(x_13);
x_15 = lean_expr_eqv(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = l_Lean_TypeClass_wakeUp(x_1, x_9, x_4);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_TypeClass_Waiter_isRoot(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 6);
lean_inc(x_10);
x_11 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_13 = l_Lean_TypeClass_newAnswer___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_TypeClass_newAnswer___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_23 = l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__4(x_2, x_18, x_20, x_21, x_22);
lean_dec(x_21);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_48; uint8_t x_49; 
x_48 = lean_array_get_size(x_19);
x_49 = l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__6(x_18, x_19, x_48, x_22);
lean_dec(x_48);
lean_dec(x_18);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = 0;
x_26 = x_50;
goto block_47;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = l_Lean_TypeClass_Context_eHasTmpMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lean_TypeClass_Context_eHasTmpMVar(x_54);
x_26 = x_55;
goto block_47;
}
else
{
lean_dec(x_51);
x_26 = x_49;
goto block_47;
}
}
block_47:
{
uint8_t x_27; 
x_27 = l_Bool_DecidableEq(x_26, x_24);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_3, 6);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 5);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 4);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 3);
lean_dec(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
lean_inc(x_2);
x_36 = lean_array_push(x_20, x_2);
lean_inc(x_19);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_10, x_1, x_37);
lean_ctor_set(x_3, 6, x_38);
x_39 = l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_2, x_19, x_22, x_3);
lean_dec(x_19);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
lean_inc(x_2);
x_40 = lean_array_push(x_20, x_2);
lean_inc(x_19);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_10, x_1, x_41);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_5);
lean_ctor_set(x_43, 2, x_6);
lean_ctor_set(x_43, 3, x_7);
lean_ctor_set(x_43, 4, x_8);
lean_ctor_set(x_43, 5, x_9);
lean_ctor_set(x_43, 6, x_42);
x_44 = l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_2, x_19, x_22, x_43);
lean_dec(x_19);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_3);
return x_57;
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
lean_object* l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_TypeClass_newAnswer___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_TypeClass_newAnswer___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
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
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_TypeClass_consume(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_7);
x_11 = lean_array_pop(x_7);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_ctor_set(x_1, 4, x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_inc(x_14);
x_17 = l_Lean_TypeClass_Context_eInstantiate___main(x_14, x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_14);
x_19 = l_Lean_TypeClass_Context_eInstantiate___main(x_14, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_TypeClass_newAnswer(x_22, x_21, x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_26);
x_27 = l_Lean_TypeClass_Context_eInfer(x_26, x_24);
lean_inc(x_26);
x_28 = l_Lean_TypeClass_Context_eInstantiate___main(x_26, x_27);
x_29 = l_Lean_TypeClass_Context__u03b1Norm(x_28);
lean_inc(x_10);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_9, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = l_Lean_TypeClass_newSubgoal(x_30, x_26, x_29, x_24, x_1);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4(x_10, x_33, x_35, x_36, x_8);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_33, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = lean_array_push(x_34, x_30);
lean_ctor_set(x_33, 0, x_41);
x_42 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_9, x_29, x_33);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_4);
lean_ctor_set(x_43, 2, x_5);
lean_ctor_set(x_43, 3, x_6);
lean_ctor_set(x_43, 4, x_11);
lean_ctor_set(x_43, 5, x_37);
lean_ctor_set(x_43, 6, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_33);
x_46 = lean_array_push(x_34, x_30);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
x_48 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_9, x_29, x_47);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_4);
lean_ctor_set(x_49, 2, x_5);
lean_ctor_set(x_49, 3, x_6);
lean_ctor_set(x_49, 4, x_11);
lean_ctor_set(x_49, 5, x_37);
lean_ctor_set(x_49, 6, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_54 = lean_ctor_get(x_1, 2);
x_55 = lean_ctor_get(x_1, 3);
x_56 = lean_ctor_get(x_1, 4);
x_57 = lean_ctor_get(x_1, 5);
x_58 = lean_ctor_get(x_1, 6);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_59 = l_Array_back___at_Lean_TypeClass_consume___spec__2(x_56);
x_60 = lean_array_pop(x_56);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_60);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_61 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_55);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_inc(x_64);
x_67 = l_Lean_TypeClass_Context_eInstantiate___main(x_64, x_66);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
lean_inc(x_64);
x_69 = l_Lean_TypeClass_Context_eInstantiate___main(x_64, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = l_Lean_TypeClass_newAnswer(x_72, x_71, x_61);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_ctor_get(x_59, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
lean_inc(x_76);
x_77 = l_Lean_TypeClass_Context_eInfer(x_76, x_74);
lean_inc(x_76);
x_78 = l_Lean_TypeClass_Context_eInstantiate___main(x_76, x_77);
x_79 = l_Lean_TypeClass_Context__u03b1Norm(x_78);
lean_inc(x_59);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_59);
x_81 = l_PersistentHashMap_find___at_Lean_TypeClass_newAnswer___spec__1(x_58, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_82 = l_Lean_TypeClass_newSubgoal(x_80, x_76, x_79, x_74, x_61);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_61);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4(x_59, x_83, x_85, x_86, x_57);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_88 = x_83;
} else {
 lean_dec_ref(x_83);
 x_88 = lean_box(0);
}
x_89 = lean_array_push(x_84, x_80);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
x_91 = l_PersistentHashMap_insert___at_Lean_TypeClass_newSubgoal___spec__2(x_58, x_79, x_90);
x_92 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_92, 0, x_52);
lean_ctor_set(x_92, 1, x_53);
lean_ctor_set(x_92, 2, x_54);
lean_ctor_set(x_92, 3, x_55);
lean_ctor_set(x_92, 4, x_60);
lean_ctor_set(x_92, 5, x_87);
lean_ctor_set(x_92, 6, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
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
lean_object* l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_TypeClass_consume___spec__4(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_environment_find(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_2);
x_8 = l_Lean_TypeClass_constNameToTypedExpr___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_TypeClass_constNameToTypedExpr___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = l_Lean_ConstantInfo_lparams(x_13);
x_17 = l_List_foldl___main___at_Lean_TypeClass_constNameToTypedExpr___spec__1(x_15, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Lean_mkConst(x_2, x_19);
x_21 = lean_instantiate_type_lparams(x_13, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_17, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_26 = l_Lean_mkConst(x_2, x_24);
x_27 = lean_instantiate_type_lparams(x_13, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = l_Array_back___at_Lean_TypeClass_generate___spec__2(x_5);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 6);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_array_pop(x_5);
lean_ctor_set(x_1, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_22 = lean_array_pop(x_5);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_6);
lean_ctor_set(x_23, 5, x_7);
lean_ctor_set(x_23, 6, x_8);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_27 = l_Lean_TypeClass_generate___closed__1;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = l_Lean_TypeClass_constNameToTypedExpr(x_32, x_30, x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_31, 2);
lean_inc(x_38);
x_39 = l_Lean_TypeClass_tryResolve(x_37, x_38, x_36, x_35);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_41, 3);
x_45 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_45, 0, x_29);
x_46 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_44, x_45);
lean_ctor_set(x_41, 3, x_46);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_47; 
lean_dec(x_31);
x_47 = lean_box(0);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_39);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_TypeClass_newConsumerNode(x_31, x_49, x_50, x_41);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
x_55 = lean_ctor_get(x_41, 2);
x_56 = lean_ctor_get(x_41, 3);
x_57 = lean_ctor_get(x_41, 4);
x_58 = lean_ctor_get(x_41, 5);
x_59 = lean_ctor_get(x_41, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
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
lean_object* x_63; 
lean_dec(x_31);
x_63 = lean_box(0);
lean_ctor_set(x_39, 1, x_62);
lean_ctor_set(x_39, 0, x_63);
return x_39;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_39);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_TypeClass_newConsumerNode(x_31, x_65, x_66, x_62);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_68 = lean_ctor_get(x_39, 1);
x_69 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
lean_inc(x_69);
lean_dec(x_39);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 5);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 6);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 lean_ctor_release(x_68, 5);
 lean_ctor_release(x_68, 6);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_closure((void*)(l_Lean_TypeClass_generate___lambda__1), 2, 1);
lean_closure_set(x_78, 0, x_29);
x_79 = l_Stack_modify___at_Lean_TypeClass_generate___spec__4(x_73, x_78);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 7, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_79);
lean_ctor_set(x_80, 4, x_74);
lean_ctor_set(x_80, 5, x_75);
lean_ctor_set(x_80, 6, x_76);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_31);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_69, 0);
lean_inc(x_83);
lean_dec(x_69);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_TypeClass_newConsumerNode(x_31, x_84, x_85, x_80);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_31);
lean_dec(x_29);
x_87 = !lean_is_exclusive(x_33);
if (x_87 == 0)
{
return x_33;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_33, 0);
x_89 = lean_ctor_get(x_33, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_33);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
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
uint8_t x_2; lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_1, 5);
lean_inc(x_29);
x_30 = l_Queue_isEmpty___rarg(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 1;
x_2 = x_31;
goto block_28;
}
else
{
uint8_t x_32; 
x_32 = 0;
x_2 = x_32;
goto block_28;
}
block_28:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 1;
x_4 = l_Bool_DecidableEq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = l_Array_isEmpty___rarg(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_String_Iterator_extract___closed__1;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = l_Array_isEmpty___rarg(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_TypeClass_step___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_TypeClass_step___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_TypeClass_generate(x_1);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l_Lean_TypeClass_consume(x_1);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = l_Array_isEmpty___rarg(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_String_Iterator_extract___closed__1;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_TypeClass_step___closed__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_TypeClass_generate(x_1);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_TypeClass_step___closed__1;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = l_Lean_TypeClass_consume(x_1);
return x_26;
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_TypeClass_resume(x_1);
return x_27;
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
lean_free_object(x_7);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
x_1 = x_6;
x_2 = x_14;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_TypeClass_synthCore___main___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
return x_24;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Level_hasMVar(x_7);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_4, x_7);
x_1 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_TypeClass_Context_uNewMeta(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_ctor_set(x_14, 1, x_7);
x_18 = lean_array_push(x_3, x_14);
x_19 = lean_array_push(x_4, x_16);
x_1 = x_8;
x_2 = x_17;
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_7);
x_24 = lean_array_push(x_3, x_23);
x_25 = lean_array_push(x_4, x_21);
x_1 = x_8;
x_2 = x_22;
x_3 = x_24;
x_4 = x_25;
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
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__1() {
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
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TypeClass_Context_Inhabited;
x_2 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.TypeClass.Synth");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TODO(dselsam): this case not yet handled");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_collectEReplacements___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_TypeClass_collectEReplacements___main___closed__3;
x_2 = lean_unsigned_to_nat(289u);
x_3 = lean_unsigned_to_nat(27u);
x_4 = l_Lean_TypeClass_collectEReplacements___main___closed__4;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
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
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_17 = lean_expr_instantiate1(x_11, x_12);
lean_dec(x_11);
x_18 = lean_array_push(x_7, x_12);
x_3 = x_17;
x_4 = x_13;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_1);
x_20 = l_Lean_LocalContext_mkForall(x_1, x_2, x_10);
lean_dec(x_10);
x_21 = l_Lean_TypeClass_Context_eNewMeta(x_20, x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
x_26 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_25, x_23);
x_27 = lean_expr_instantiate1(x_11, x_26);
lean_dec(x_11);
lean_ctor_set(x_21, 1, x_12);
x_28 = lean_array_push(x_6, x_21);
x_29 = lean_array_push(x_7, x_26);
x_3 = x_27;
x_4 = x_13;
x_5 = x_24;
x_6 = x_28;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_31);
x_34 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_33, x_31);
x_35 = lean_expr_instantiate1(x_11, x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_12);
x_37 = lean_array_push(x_6, x_36);
x_38 = lean_array_push(x_7, x_34);
x_3 = x_35;
x_4 = x_13;
x_5 = x_32;
x_6 = x_37;
x_7 = x_38;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = l_Lean_TypeClass_collectEReplacements___main___closed__2;
x_43 = l_Lean_TypeClass_collectEReplacements___main___closed__5;
x_44 = lean_panic_fn(x_43);
return x_44;
}
}
}
}
lean_object* l_Lean_TypeClass_collectEReplacements___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_TypeClass_collectEReplacements___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
x_2 = lean_alloc_closure((void*)(l_Lean_TypeClass_collectEReplacements___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_TypeClass_collectEReplacements___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_TypeClass_collectEReplacements___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
lean_object* _init_l_Lean_TypeClass_preprocessForOutParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_TypeClass_collectEReplacements___main___closed__3;
x_2 = lean_unsigned_to_nat(305u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_TypeClass_preprocessForOutParams___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_TypeClass_preprocessForOutParams(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_127; 
x_127 = l_Lean_Expr_hasMVar(x_2);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = l_Lean_Expr_getAppFn___main(x_2);
x_129 = l_Lean_Expr_isConst(x_128);
if (x_129 == 0)
{
uint8_t x_130; 
lean_dec(x_128);
x_130 = 0;
x_3 = x_130;
goto block_126;
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Expr_constName_x21(x_128);
lean_dec(x_128);
lean_inc(x_1);
x_132 = lean_has_out_params(x_1, x_131);
if (x_132 == 0)
{
x_3 = x_129;
goto block_126;
}
else
{
uint8_t x_133; 
x_133 = 0;
x_3 = x_133;
goto block_126;
}
}
}
else
{
uint8_t x_134; 
x_134 = 0;
x_3 = x_134;
goto block_126;
}
block_126:
{
uint8_t x_4; uint8_t x_5; 
x_4 = 1;
x_5 = l_Bool_DecidableEq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_118; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_LocalContext_Inhabited___closed__2;
x_8 = l_Array_empty___closed__1;
lean_inc(x_2);
x_9 = l_Lean_TypeClass_introduceLocals___main(x_6, x_7, x_8, x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = l_Lean_Expr_getAppFn___main(x_2);
x_16 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_6);
x_17 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
lean_inc(x_2);
x_21 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_18, x_20);
x_118 = l_Lean_Expr_isConst(x_15);
if (x_118 == 0)
{
x_22 = x_4;
goto block_117;
}
else
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_Expr_constName_x21(x_15);
lean_inc(x_1);
x_120 = lean_is_class(x_1, x_119);
if (x_120 == 0)
{
x_22 = x_4;
goto block_117;
}
else
{
uint8_t x_121; 
x_121 = 0;
x_22 = x_121;
goto block_117;
}
}
block_117:
{
uint8_t x_23; 
x_23 = l_Bool_DecidableEq(x_22, x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_2);
x_24 = l_Lean_Expr_constLevels_x21(x_15);
x_25 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_26 = l_Lean_TypeClass_collectUReplacements___main(x_24, x_25, x_8, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = l_Array_isEmpty___rarg(x_29);
x_33 = l_Bool_DecidableEq(x_32, x_4);
x_34 = l_Array_toList___rarg(x_21);
lean_dec(x_21);
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = l_Lean_Expr_constName_x21(x_15);
lean_dec(x_15);
x_36 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
lean_inc(x_36);
x_37 = l_Lean_mkConst(x_35, x_36);
x_38 = l_Lean_Expr_constName_x21(x_37);
x_39 = lean_environment_find(x_1, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_36);
x_68 = l_Lean_Expr_Inhabited;
x_69 = l_Lean_TypeClass_preprocessForOutParams___closed__2;
x_70 = lean_panic_fn(x_69);
lean_inc(x_11);
x_71 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_13, x_70, x_34, x_28, x_8, x_8);
x_40 = x_71;
goto block_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_instantiate_type_lparams(x_72, x_36);
lean_inc(x_11);
x_74 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_13, x_73, x_34, x_28, x_8, x_8);
x_40 = x_74;
goto block_67;
}
block_67:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
x_47 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_46, x_46, x_6, x_37);
lean_dec(x_46);
x_48 = l_Lean_LocalContext_mkForall(x_11, x_13, x_47);
lean_dec(x_47);
lean_dec(x_13);
lean_ctor_set(x_42, 1, x_45);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_40, 0, x_48);
if (lean_is_scalar(x_31)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_31;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_53 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_52, x_52, x_6, x_37);
lean_dec(x_52);
x_54 = l_Lean_LocalContext_mkForall(x_11, x_13, x_53);
lean_dec(x_53);
lean_dec(x_13);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_29);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_40, 1, x_55);
lean_ctor_set(x_40, 0, x_54);
if (lean_is_scalar(x_31)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_31;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_40);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_40, 1);
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_57);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_60, x_60, x_6, x_37);
lean_dec(x_60);
x_63 = l_Lean_LocalContext_mkForall(x_11, x_13, x_62);
lean_dec(x_62);
lean_dec(x_13);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_29);
lean_ctor_set(x_64, 1, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_31)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_31;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Lean_Expr_constName_x21(x_15);
x_76 = lean_environment_find(x_1, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_30);
x_105 = l_Lean_Expr_Inhabited;
x_106 = l_Lean_TypeClass_preprocessForOutParams___closed__2;
x_107 = lean_panic_fn(x_106);
lean_inc(x_11);
x_108 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_13, x_107, x_34, x_28, x_8, x_8);
x_77 = x_108;
goto block_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_76, 0);
lean_inc(x_109);
lean_dec(x_76);
x_110 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
x_111 = lean_instantiate_type_lparams(x_109, x_110);
lean_inc(x_11);
x_112 = l_Lean_TypeClass_collectEReplacements___main(x_11, x_13, x_111, x_34, x_28, x_8, x_8);
x_77 = x_112;
goto block_104;
}
block_104:
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_77, 1);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
x_84 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_83, x_83, x_6, x_15);
lean_dec(x_83);
x_85 = l_Lean_LocalContext_mkForall(x_11, x_13, x_84);
lean_dec(x_84);
lean_dec(x_13);
lean_ctor_set(x_79, 1, x_82);
lean_ctor_set(x_79, 0, x_29);
lean_ctor_set(x_77, 0, x_85);
if (lean_is_scalar(x_31)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_31;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_77, 0);
x_88 = lean_ctor_get(x_79, 0);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_79);
x_90 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_89, x_89, x_6, x_15);
lean_dec(x_89);
x_91 = l_Lean_LocalContext_mkForall(x_11, x_13, x_90);
lean_dec(x_90);
lean_dec(x_13);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_29);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_77, 1, x_92);
lean_ctor_set(x_77, 0, x_91);
if (lean_is_scalar(x_31)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_31;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_77);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_77, 1);
x_95 = lean_ctor_get(x_77, 0);
lean_inc(x_94);
lean_inc(x_95);
lean_dec(x_77);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_97, x_97, x_6, x_15);
lean_dec(x_97);
x_100 = l_Lean_LocalContext_mkForall(x_11, x_13, x_99);
lean_dec(x_99);
lean_dec(x_13);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_29);
lean_ctor_set(x_101, 1, x_96);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
if (lean_is_scalar(x_31)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_31;
}
lean_ctor_set(x_103, 0, x_95);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_113 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
if (lean_is_scalar(x_14)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_14;
}
lean_ctor_set(x_114, 0, x_2);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_TypeClass_Context_Inhabited___closed__1;
if (lean_is_scalar(x_12)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_12;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_122 = l_Lean_TypeClass_collectEReplacements___main___closed__1;
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_2);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_TypeClass_Context_Inhabited___closed__1;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_TypeClass_preprocessForOutParams(x_4, x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_8);
x_9 = l_Lean_TypeClass_Context_eNewMeta(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_TypeClass_Context__u03b1Norm(x_8);
x_13 = lean_box(1);
lean_inc(x_10);
lean_inc(x_11);
x_14 = l_Lean_TypeClass_newSubgoal(x_13, x_11, x_12, x_10, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 2);
lean_dec(x_17);
lean_ctor_set(x_15, 2, x_10);
x_18 = l_Lean_TypeClass_synthCore___main(x_2, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_22);
lean_inc(x_1);
x_23 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_22, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_22);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_TypeClass_Context_eInstantiate___main(x_25, x_21);
lean_inc(x_27);
x_28 = l_Lean_TypeClass_Context_eHasTmpMVar(x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_31; 
lean_dec(x_27);
x_31 = l_Lean_TypeClass_synth___closed__1;
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_TypeClass_Context_eInstantiate___main(x_32, x_21);
lean_inc(x_33);
x_34 = l_Lean_TypeClass_Context_eHasTmpMVar(x_33);
x_35 = 1;
x_36 = l_Bool_DecidableEq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_20);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_33);
x_38 = l_Lean_TypeClass_synth___closed__1;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_23, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_23, 0);
lean_dec(x_42);
x_43 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_44 = l_Lean_TypeClass_synth___closed__2;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lean_TypeClass_synth___closed__3;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_expr_dbg_to_string(x_22);
lean_dec(x_22);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 0, x_49);
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_23);
x_50 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_51 = l_Lean_TypeClass_synth___closed__2;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_TypeClass_synth___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_expr_dbg_to_string(x_22);
lean_dec(x_22);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_20);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_15, 0);
x_63 = lean_ctor_get(x_15, 1);
x_64 = lean_ctor_get(x_15, 3);
x_65 = lean_ctor_get(x_15, 4);
x_66 = lean_ctor_get(x_15, 5);
x_67 = lean_ctor_get(x_15, 6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_15);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_10);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_66);
lean_ctor_set(x_68, 6, x_67);
x_69 = l_Lean_TypeClass_synthCore___main(x_2, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_73);
lean_inc(x_1);
x_74 = l_Lean_TypeClass_Context_eUnify___main(x_1, x_73, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; 
lean_dec(x_73);
lean_dec(x_1);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = l_Lean_TypeClass_Context_eInstantiate___main(x_75, x_72);
lean_inc(x_77);
x_78 = l_Lean_TypeClass_Context_eHasTmpMVar(x_77);
x_79 = 1;
x_80 = l_Bool_DecidableEq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_71);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_77);
x_82 = l_Lean_TypeClass_synth___closed__1;
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_76;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_71);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_72);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_84 = x_74;
} else {
 lean_dec_ref(x_74);
 x_84 = lean_box(0);
}
x_85 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_86 = l_Lean_TypeClass_synth___closed__2;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_TypeClass_synth___closed__3;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_expr_dbg_to_string(x_73);
lean_dec(x_73);
x_91 = lean_string_append(x_89, x_90);
lean_dec(x_90);
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_71);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_11);
lean_dec(x_1);
x_93 = lean_ctor_get(x_69, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_95 = x_69;
} else {
 lean_dec_ref(x_69);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_14);
if (x_97 == 0)
{
return x_14;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_14, 0);
x_99 = lean_ctor_get(x_14, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_14);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Class(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
lean_object* initialize_Init_Lean_TypeClass_Context(lean_object*);
lean_object* initialize_Init_Data_PersistentHashMap(lean_object*);
lean_object* initialize_Init_Data_Stack(lean_object*);
lean_object* initialize_Init_Data_Queue(lean_object*);
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
res = initialize_Init_Data_PersistentHashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stack(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TypeClass_TypedExpr_HasToString___closed__1 = _init_l_Lean_TypeClass_TypedExpr_HasToString___closed__1();
lean_mark_persistent(l_Lean_TypeClass_TypedExpr_HasToString___closed__1);
l_Lean_TypeClass_TypedExpr_Inhabited___closed__1 = _init_l_Lean_TypeClass_TypedExpr_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TypeClass_TypedExpr_Inhabited___closed__1);
l_Lean_TypeClass_TypedExpr_Inhabited = _init_l_Lean_TypeClass_TypedExpr_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_TypedExpr_Inhabited);
l_Lean_TypeClass_Answer_HasToString___closed__1 = _init_l_Lean_TypeClass_Answer_HasToString___closed__1();
lean_mark_persistent(l_Lean_TypeClass_Answer_HasToString___closed__1);
l_Lean_TypeClass_Answer_Inhabited = _init_l_Lean_TypeClass_Answer_Inhabited();
lean_mark_persistent(l_Lean_TypeClass_Answer_Inhabited);
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
l_Lean_TypeClass_collectEReplacements___main___closed__1 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__1();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__1);
l_Lean_TypeClass_collectEReplacements___main___closed__2 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__2();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__2);
l_Lean_TypeClass_collectEReplacements___main___closed__3 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__3();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__3);
l_Lean_TypeClass_collectEReplacements___main___closed__4 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__4();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__4);
l_Lean_TypeClass_collectEReplacements___main___closed__5 = _init_l_Lean_TypeClass_collectEReplacements___main___closed__5();
lean_mark_persistent(l_Lean_TypeClass_collectEReplacements___main___closed__5);
l_Lean_TypeClass_preprocessForOutParams___closed__1 = _init_l_Lean_TypeClass_preprocessForOutParams___closed__1();
lean_mark_persistent(l_Lean_TypeClass_preprocessForOutParams___closed__1);
l_Lean_TypeClass_preprocessForOutParams___closed__2 = _init_l_Lean_TypeClass_preprocessForOutParams___closed__2();
lean_mark_persistent(l_Lean_TypeClass_preprocessForOutParams___closed__2);
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
