// Lean compiler output
// Module: Lean.Elab.WhereFinally
// Imports: Lean.Parser.Term
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
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_none;
static lean_object* l_Lean_Elab_instInhabitedWhereFinallyView___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_ctorIdx___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object*);
static lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__1;
static lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__0;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedWhereFinallyView;
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WhereFinallyView_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedWhereFinallyView___closed__0() {
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
static lean_object* _init_l_Lean_Elab_instInhabitedWhereFinallyView() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedWhereFinallyView___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WhereFinallyView_none() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedWhereFinallyView___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_isMissing(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isMissing(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_WhereFinallyView_isNone(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`where ... finally` does not currently support any named sub-sections `| sectionName => ...`", 92, 92);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Syntax_getArg(x_6, x_7);
x_18 = l_Lean_Syntax_getArg(x_17, x_8);
lean_dec(x_17);
x_19 = l_Lean_Syntax_isMissing(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
goto block_16;
}
else
{
if (x_9 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_10, lean_box(0), x_20);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_11);
return x_22;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__1;
x_14 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_3, x_13);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_3, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_isMissing(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_5);
lean_inc(x_6);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(x_11);
lean_inc(x_6);
lean_inc_ref(x_13);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___boxed), 12, 11);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_10);
lean_closure_set(x_15, 6, x_7);
lean_closure_set(x_15, 7, x_9);
lean_closure_set(x_15, 8, x_14);
lean_closure_set(x_15, 9, x_6);
lean_closure_set(x_15, 10, x_13);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_6, lean_box(0), x_16);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec_ref(x_2);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_3);
x_23 = lean_apply_2(x_6, lean_box(0), x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_2(x_6, lean_box(0), x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_mkWhereFinallyView___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_9);
x_14 = l_Lean_Elab_mkWhereFinallyView___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_WhereFinally(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedWhereFinallyView___closed__0 = _init_l_Lean_Elab_instInhabitedWhereFinallyView___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedWhereFinallyView___closed__0);
l_Lean_Elab_instInhabitedWhereFinallyView = _init_l_Lean_Elab_instInhabitedWhereFinallyView();
lean_mark_persistent(l_Lean_Elab_instInhabitedWhereFinallyView);
l_Lean_Elab_WhereFinallyView_none = _init_l_Lean_Elab_WhereFinallyView_none();
lean_mark_persistent(l_Lean_Elab_WhereFinallyView_none);
l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__0 = _init_l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__0);
l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__1 = _init_l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__1();
lean_mark_persistent(l_Lean_Elab_mkWhereFinallyView___redArg___lam__3___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
