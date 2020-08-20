// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Init Lean.Delaborator Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter
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
extern lean_object* l_Lean_Parser_builtinTokenTable;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2;
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPTerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1;
extern lean_object* l_Lean_ppExprFnRef;
extern lean_object* l_Lean_Meta_run___rarg___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_delab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__4;
lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_registerPPTerm(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__3;
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_PrettyPrinter_parenthesizeTerm(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_PrettyPrinter_formatTerm(x_1, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = l_Lean_delab(x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_PrettyPrinter_ppTerm(x_1, x_7, x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_PrettyPrinter_parenthesizeCommand(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_PrettyPrinter_formatCommand(x_1, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n\n");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lean_PrettyPrinter_ppCommand(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_17);
x_4 = x_13;
x_5 = x_20;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Syntax_reprint___main(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = l_Lean_Meta_isClassQuick___main___closed__1;
x_9 = l_unreachable_x21___rarg(x_8);
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Syntax_getArgs(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Array_extract___rarg(x_12, x_14, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(x_1, x_2, x_15, x_5, x_16, x_3, x_4);
lean_dec(x_15);
return x_17;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_ppModule(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<pretty printer error: ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_registerPPTerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = 0;
x_8 = 1;
x_9 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 2, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 5, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 6, x_8);
x_10 = l_Array_empty___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1000u);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_11);
lean_ctor_set(x_13, 4, x_12);
x_14 = l_Lean_Meta_run___rarg___closed__5;
x_15 = l_Lean_NameGenerator_Inhabited___closed__3;
x_16 = l_Lean_TraceState_Inhabited___closed__1;
x_17 = l_Std_PersistentArray_empty___closed__3;
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
x_19 = l_Lean_PrettyPrinter_ppExpr(x_1, x_6, x_13, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Exception_toStr(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__2;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_7);
x_26 = l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__4;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_7);
return x_27;
}
}
}
lean_object* l_Lean_PrettyPrinter_registerPPTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Parser_builtinTokenTable;
x_3 = lean_io_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_registerPPTerm___lambda__1), 6, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l_Lean_ppExprFnRef;
x_8 = lean_io_ref_set(x_7, x_6, x_5);
return x_8;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Delaborator(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Delaborator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1);
l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2);
l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__1);
l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__2);
l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__3);
l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPTerm___lambda__1___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
