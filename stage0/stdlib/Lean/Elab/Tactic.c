// Lean compiler output
// Module: Lean.Elab.Tactic
// Imports: Lean.Elab.Term Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Induction Lean.Elab.Tactic.Generalize Lean.Elab.Tactic.Injection Lean.Elab.Tactic.Match Lean.Elab.Tactic.Rewrite Lean.Elab.Tactic.Location Lean.Elab.Tactic.SimpTrace Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Simproc Lean.Elab.Tactic.BuiltinTactic Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv Lean.Elab.Tactic.Delta Lean.Elab.Tactic.Meta Lean.Elab.Tactic.Unfold Lean.Elab.Tactic.Calc Lean.Elab.Tactic.Congr Lean.Elab.Tactic.Guard Lean.Elab.Tactic.RCases Lean.Elab.Tactic.Repeat Lean.Elab.Tactic.Ext Lean.Elab.Tactic.Change Lean.Elab.Tactic.FalseOrByContra Lean.Elab.Tactic.Omega Lean.Elab.Tactic.Simpa Lean.Elab.Tactic.NormCast Lean.Elab.Tactic.Symm Lean.Elab.Tactic.SolveByElim Lean.Elab.Tactic.LibrarySearch Lean.Elab.Tactic.ShowTerm Lean.Elab.Tactic.Rfl Lean.Elab.Tactic.Rewrites Lean.Elab.Tactic.DiscrTreeKey Lean.Elab.Tactic.BVDecide Lean.Elab.Tactic.BoolToPropSimps Lean.Elab.Tactic.Classical Lean.Elab.Tactic.Grind Lean.Elab.Tactic.Monotonicity Lean.Elab.Tactic.Try Lean.Elab.Tactic.AsAuxLemma Lean.Elab.Tactic.TreeTacAttr Lean.Elab.Tactic.ExposeNames Lean.Elab.Tactic.SimpArith Lean.Elab.Tactic.Lets
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
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_tacticGet__elem__tactic__trivial__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_tacticGet__elem__tactic__trivial__1___closed__4;
static lean_object* l_tacticGet__elem__tactic__trivial__1___closed__5;
static lean_object* l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__1;
LEAN_EXPORT lean_object* l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Rfl_evalApplyRfl___spec__1___rarg(lean_object*);
static lean_object* l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__2;
static lean_object* l_tacticGet__elem__tactic__trivial__1___closed__2;
LEAN_EXPORT lean_object* l_tacticGet__elem__tactic__trivial__1;
static lean_object* l_tacticGet__elem__tactic__trivial__1___closed__1;
static lean_object* _init_l_tacticGet__elem__tactic__trivial__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic_trivial_1", 31, 31);
return x_1;
}
}
static lean_object* _init_l_tacticGet__elem__tactic__trivial__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticGet__elem__tactic__trivial__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticGet__elem__tactic__trivial__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get_elem_tactic_trivial", 23, 23);
return x_1;
}
}
static lean_object* _init_l_tacticGet__elem__tactic__trivial__1___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticGet__elem__tactic__trivial__1___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticGet__elem__tactic__trivial__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticGet__elem__tactic__trivial__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticGet__elem__tactic__trivial__1___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticGet__elem__tactic__trivial__1() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticGet__elem__tactic__trivial__1___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`get_elem_tactic_trivial` has been renamed to `get_elem_tactic_extensible`", 74, 74);
return x_1;
}
}
static lean_object* _init_l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_tacticGet__elem__tactic__trivial__1___closed__2;
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Rfl_evalApplyRfl___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__2;
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Induction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Delta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Calc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Congr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Guard(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_RCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Omega(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Symm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SolveByElim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_LibrarySearch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ShowTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rfl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_DiscrTreeKey(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Classical(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_TreeTacAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SimpArith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Lets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Delta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Calc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Congr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Guard(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Change(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simpa(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_NormCast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Symm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SolveByElim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_LibrarySearch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ShowTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rfl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrites(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Classical(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Monotonicity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_AsAuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_TreeTacAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpArith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Lets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_tacticGet__elem__tactic__trivial__1___closed__1 = _init_l_tacticGet__elem__tactic__trivial__1___closed__1();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial__1___closed__1);
l_tacticGet__elem__tactic__trivial__1___closed__2 = _init_l_tacticGet__elem__tactic__trivial__1___closed__2();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial__1___closed__2);
l_tacticGet__elem__tactic__trivial__1___closed__3 = _init_l_tacticGet__elem__tactic__trivial__1___closed__3();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial__1___closed__3);
l_tacticGet__elem__tactic__trivial__1___closed__4 = _init_l_tacticGet__elem__tactic__trivial__1___closed__4();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial__1___closed__4);
l_tacticGet__elem__tactic__trivial__1___closed__5 = _init_l_tacticGet__elem__tactic__trivial__1___closed__5();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial__1___closed__5);
l_tacticGet__elem__tactic__trivial__1 = _init_l_tacticGet__elem__tactic__trivial__1();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial__1);
l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__1 = _init_l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__1();
lean_mark_persistent(l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__1);
l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__2 = _init_l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__2();
lean_mark_persistent(l___aux__Lean__Elab__Tactic______elabRules__tacticGet__elem__tactic__trivial__1__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
