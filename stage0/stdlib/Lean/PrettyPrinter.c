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
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_CoreM_run_x27___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Core_ECoreM_inhabited___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1;
extern lean_object* l_Lean_ppExprFnRef;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_toECoreM___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_PrettyPrinter_ppExprFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4;
lean_object* l_Lean_PrettyPrinter_registerPPTerm(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1;
lean_object* l_Lean_Core_getRef___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_toECoreM___rarg___closed__1;
extern lean_object* l_Lean_Core_Exception_inhabited;
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getTraceState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2;
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_PrettyPrinter_parenthesizeTerm(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_PrettyPrinter_formatTerm(x_6, x_2, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_delab(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_ppTerm(x_9, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_PrettyPrinter_parenthesizeCommand(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_PrettyPrinter_formatCommand(x_6, x_2, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
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
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_PrettyPrinter_ppCommand(x_11, x_5, x_6, x_7);
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
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_17);
x_3 = x_13;
x_4 = x_20;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* _init_l_Lean_PrettyPrinter_ppModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Exception_inhabited;
x_2 = lean_alloc_closure((void*)(l_Lean_Core_ECoreM_inhabited___rarg___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_reprint___main(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_PrettyPrinter_ppModule___closed__1;
x_9 = l_unreachable_x21___rarg(x_8);
x_10 = lean_apply_3(x_9, x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Syntax_getArgs(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Array_extract___rarg(x_12, x_14, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(x_1, x_15, x_5, x_16, x_2, x_3, x_4);
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
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_ppModule(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<pretty printer error: ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_44 = l_Lean_getMaxRecDepth(x_4);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Lean_NameGenerator_Inhabited___closed__3;
x_49 = l_Lean_TraceState_Inhabited___closed__1;
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_box(0);
x_52 = lean_io_mk_ref(x_50, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_83 = l_Lean_Core_getRef___rarg(x_47, x_53, x_54);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_MetaM_toECoreM___rarg___closed__3;
x_87 = lean_io_mk_ref(x_86, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_MetaM_toECoreM___rarg___closed__1;
x_91 = l_Array_empty___closed__1;
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_3);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_Lean_Meta_setMCtx(x_2, x_92, x_88, x_47, x_53, x_89);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_53);
lean_inc(x_47);
lean_inc(x_88);
x_95 = l_Lean_PrettyPrinter_ppExpr(x_5, x_92, x_88, x_47, x_53, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_84);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_io_ref_get(x_88, x_97);
lean_dec(x_88);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Core_getEnv___rarg(x_53, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_96);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_55 = x_104;
x_56 = x_102;
goto block_82;
}
else
{
lean_object* x_105; 
lean_dec(x_88);
x_105 = lean_ctor_get(x_95, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 2)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_84);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_dec(x_95);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_55 = x_108;
x_56 = x_106;
goto block_82;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
lean_dec(x_95);
x_110 = l_Lean_Meta_Exception_toMessageData(x_105);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_84);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_55 = x_112;
x_56 = x_109;
goto block_82;
}
}
block_16:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_io_error_to_string(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4;
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_10);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
return x_15;
}
}
block_22:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_6 = x_19;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_6 = x_21;
goto block_16;
}
}
block_43:
{
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_17 = x_26;
goto block_22;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Lean_KernelException_toMessageData(x_27, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_MessageData_formatAux___main(x_30, x_29);
x_32 = l_Lean_Options_empty;
x_33 = l_Lean_Format_pretty(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
x_17 = x_35;
goto block_22;
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_box(0);
x_38 = l_Lean_MessageData_formatAux___main(x_37, x_36);
x_39 = l_Lean_Options_empty;
x_40 = l_Lean_Format_pretty(x_38, x_39);
x_41 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_24);
x_17 = x_42;
goto block_22;
}
}
}
block_82:
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Core_getTraceState___rarg(x_53, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Std_PersistentArray_forM___at_Lean_Core_CoreM_run_x27___spec__3(x_61, x_47, x_53, x_60);
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_23 = x_57;
x_24 = x_63;
goto block_43;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_57);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_23 = x_64;
x_24 = x_65;
goto block_43;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
lean_dec(x_55);
x_67 = l_Lean_Core_getTraceState___rarg(x_53, x_56);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Std_PersistentArray_forM___at_Lean_Core_CoreM_run_x27___spec__3(x_70, x_47, x_53, x_69);
lean_dec(x_47);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_io_ref_get(x_53, x_72);
lean_dec(x_53);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
lean_dec(x_66);
lean_ctor_set(x_73, 0, x_76);
x_17 = x_73;
goto block_22;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_17 = x_79;
goto block_22;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_66);
lean_dec(x_53);
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_dec(x_71);
x_23 = x_80;
x_24 = x_81;
goto block_43;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppExprFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_ppExprFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_ppExprFn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_PrettyPrinter_registerPPTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprFnUnsafe), 5, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_registerPPTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_ppExprFnRef;
x_3 = l_Lean_PrettyPrinter_registerPPTerm___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
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
l_Lean_PrettyPrinter_ppModule___closed__1 = _init_l_Lean_PrettyPrinter_ppModule___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppModule___closed__1);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4);
l_Lean_PrettyPrinter_registerPPTerm___closed__1 = _init_l_Lean_PrettyPrinter_registerPPTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPTerm___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
