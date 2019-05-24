// Lean compiler output
// Module: init.lean.parser.rec
// Imports: init.control.reader init.lean.parser.parsec init.fix
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
obj* l_Lean_Parser_RecT_Alternative(obj*, obj*, obj*);
obj* l_fixCore___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadRec_base(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadRec_trans___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadRec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_MonadExcept___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_HasMonadLift___boxed(obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_RecT_MonadFunctor(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_HasMonadLift___rarg(obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadRec_base___closed__1;
obj* l_Lean_Parser_RecT_run(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadRec_base___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Monad___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_RecT_MonadExcept___rarg(obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadRec_trans(obj*, obj*, obj*, obj*);
obj* l_StateT_MonadExcept___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Alternative___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_run___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_runParsec___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_HasMonadLift(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_runParsec(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadRec_trans___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Alternative___rarg(obj*, obj*);
obj* l_ReaderT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_runParsec___rarg(obj*, obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_Lean_Parser_RecT_recurse___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_run___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_MonadFunctor___rarg(obj*);
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
obj* l_Lean_Parser_RecT_Monad(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_recurse(obj*, obj*, obj*, obj*);
obj* l_ReaderT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_RecT_MonadExcept(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Monad___rarg(obj*);
obj* l_Lean_Parser_RecT_MonadFunctor___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_recurse___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Parser_RecT_recurse(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
return x_5;
}
}
obj* l_Lean_Parser_RecT_recurse___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_RecT_recurse(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_RecT_run___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_MonadExcept___rarg___lambda__2), 3, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::apply_1(x_1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_RecT_run(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_run___rarg), 3, 0);
return x_6;
}
}
obj* l_Lean_Parser_RecT_run___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_RecT_run(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("RecT.runParsec: no progress");
return x_1;
}
}
obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_4, x_5, x_3, x_3);
return x_6;
}
}
obj* l_Lean_Parser_RecT_runParsec___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_runParsec___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_MonadExcept___rarg___lambda__2), 3, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::apply_1(x_2, x_6);
return x_7;
}
}
obj* l_Lean_Parser_RecT_runParsec(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_runParsec___rarg), 3, 0);
return x_7;
}
}
obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_RecT_runParsec___rarg___lambda__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_RecT_runParsec___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_RecT_runParsec(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_RecT_Monad___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_RecT_Monad(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_Monad___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_Parser_RecT_Monad___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_RecT_Monad(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_RecT_Alternative___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ReaderT_Alternative___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_RecT_Alternative(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_Alternative___rarg), 2, 0);
return x_4;
}
}
obj* l_Lean_Parser_RecT_Alternative___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_RecT_Alternative(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_RecT_HasMonadLift___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
return x_2;
}
}
obj* l_Lean_Parser_RecT_HasMonadLift(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_HasMonadLift___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_Parser_RecT_HasMonadLift___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_RecT_HasMonadLift(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_RecT_MonadExcept___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_MonadExcept___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_RecT_MonadExcept(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_MonadExcept___rarg), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_RecT_MonadExcept___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_RecT_MonadExcept(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_1);
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_5, 0, lean::box(0));
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, lean::box(0));
lean::closure_set(x_5, 3, x_1);
lean::closure_set(x_5, 4, x_1);
x_6 = l_Lean_Parser_monadParsecTrans___rarg(x_4, x_5, x_3);
return x_6;
}
}
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg), 3, 0);
return x_4;
}
}
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_RecT_MonadFunctor___rarg(obj* x_1) {
_start:
{
obj* x_2; 
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, lean::box(0));
lean::closure_set(x_2, 3, x_1);
lean::closure_set(x_2, 4, x_1);
return x_2;
}
}
obj* l_Lean_Parser_RecT_MonadFunctor(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_MonadFunctor___rarg), 1, 0);
return x_5;
}
}
obj* l_Lean_Parser_RecT_MonadFunctor___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_RecT_MonadFunctor(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadRec_trans___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::apply_1(x_2, x_4);
x_6 = lean::apply_2(x_1, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadRec_trans(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadRec_trans___rarg___boxed), 4, 0);
return x_5;
}
}
obj* l_Lean_Parser_MonadRec_trans___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadRec_trans___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadRec_trans___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadRec_trans(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_Lean_Parser_MonadRec_base___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadRec_base(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadRec_base___closed__1;
return x_5;
}
}
obj* l_Lean_Parser_MonadRec_base___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadRec_base(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_parser_parsec(obj*);
obj* initialize_init_fix(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_rec(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
if (io_result_is_error(w)) return w;
w = initialize_init_fix(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1);
l_Lean_Parser_MonadRec_base___closed__1 = _init_l_Lean_Parser_MonadRec_base___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadRec_base___closed__1);
return w;
}
