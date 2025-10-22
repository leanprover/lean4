// Lean compiler output
// Module: Lean.Elab.Tactic.Show
// Imports: public import Lean.Elab.Tactic.Change
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
static lean_object* l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4;
lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_elabChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5;
lean_object* l_List_reverseAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabShow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalShow___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3;
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'show' tactic failed, pattern", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis not definitionally equal to target", 38, 38);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1;
x_5 = l_Lean_indentExpr(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_indentExpr(x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'show' tactic failed, no goals unify with the given pattern.\n\nIn the first goal, the pattern", 92, 92);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis not definitionally equal to the target", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n(Errors for other goals omitted)", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1;
x_5 = l_Lean_indentExpr(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_indentExpr(x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_17 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = l_Lean_MVarId_replaceTargetDefEq(x_5, x_21, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_List_appendTR___redArg(x_22, x_6);
x_27 = l_List_reverseAux___redArg(x_7, x_26);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_24);
x_28 = l_Lean_Elab_Tactic_setGoals___redArg(x_18, x_9, x_25);
lean_dec(x_9);
return x_28;
}
else
{
uint8_t x_29; 
lean_free_object(x_18);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = l_Lean_MVarId_replaceTargetDefEq(x_5, x_33, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_List_appendTR___redArg(x_34, x_6);
x_39 = l_List_reverseAux___redArg(x_7, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Tactic_setGoals___redArg(x_40, x_9, x_37);
lean_dec(x_9);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_44 = x_35;
} else {
 lean_dec_ref(x_35);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("show", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_2);
x_15 = l_Lean_MVarId_getType(x_2, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_2);
x_18 = l_Lean_MVarId_getTag(x_2, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange), 12, 3);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_5);
x_22 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1;
x_23 = 0;
x_24 = lean_box(x_23);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed), 16, 7);
lean_closure_set(x_25, 0, x_21);
lean_closure_set(x_25, 1, x_19);
lean_closure_set(x_25, 2, x_22);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_3);
lean_closure_set(x_25, 6, x_4);
x_26 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(x_2, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_4);
x_18 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l_Lean_Elab_Tactic_getGoals___redArg(x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
x_17 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec_ref(x_15);
x_17 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0;
x_19 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(x_1, x_2, x_17, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_19;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_39; uint8_t x_58; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_28 = x_3;
} else {
 lean_dec_ref(x_3);
 x_28 = lean_box(0);
}
x_58 = l_List_isEmpty___redArg(x_27);
if (x_58 == 0)
{
x_39 = x_58;
goto block_57;
}
else
{
uint8_t x_59; 
x_59 = l_List_isEmpty___redArg(x_4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_60 == 0)
{
x_39 = x_58;
goto block_57;
}
else
{
x_39 = x_59;
goto block_57;
}
}
else
{
x_39 = x_59;
goto block_57;
}
}
block_38:
{
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_32);
x_34 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_29, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
if (lean_is_scalar(x_28)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_28;
}
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_4);
x_3 = x_27;
x_4 = x_36;
x_13 = x_35;
goto _start;
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
else
{
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_32;
}
}
block_57:
{
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1;
lean_inc(x_4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal), 14, 5);
lean_closure_set(x_44, 0, x_1);
lean_closure_set(x_44, 1, x_26);
lean_closure_set(x_44, 2, x_27);
lean_closure_set(x_44, 3, x_4);
lean_closure_set(x_44, 4, x_43);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_45 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_41);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = 1;
x_49 = l_Lean_Exception_isInterrupt(x_46);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Exception_isRuntime(x_46);
lean_dec(x_46);
x_29 = x_41;
x_30 = x_47;
x_31 = x_48;
x_32 = x_45;
x_33 = x_50;
goto block_38;
}
else
{
lean_dec(x_46);
x_29 = x_41;
x_30 = x_47;
x_31 = x_48;
x_32 = x_45;
x_33 = x_49;
goto block_38;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_28);
lean_dec(x_2);
x_55 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1;
x_56 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(x_1, x_26, x_27, x_4, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabShow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getGoals___redArg(x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(x_1, x_16, x_12, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg(x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0;
x_2 = l_Lean_Elab_Tactic_evalShow___closed__2;
x_3 = l_Lean_Elab_Tactic_evalShow___closed__1;
x_4 = l_Lean_Elab_Tactic_evalShow___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalShow___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_elabShow(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalShow", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalShow___closed__2;
x_3 = l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalShow___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalShow___closed__3;
x_4 = l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalShow), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Show(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Change(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0);
l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1 = _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__1);
l_Lean_Elab_Tactic_evalShow___closed__0 = _init_l_Lean_Elab_Tactic_evalShow___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___closed__0);
l_Lean_Elab_Tactic_evalShow___closed__1 = _init_l_Lean_Elab_Tactic_evalShow___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___closed__1);
l_Lean_Elab_Tactic_evalShow___closed__2 = _init_l_Lean_Elab_Tactic_evalShow___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___closed__2);
l_Lean_Elab_Tactic_evalShow___closed__3 = _init_l_Lean_Elab_Tactic_evalShow___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___closed__3);
l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0 = _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0);
l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1 = _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1);
l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2 = _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2);
l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__3 = _init_l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
